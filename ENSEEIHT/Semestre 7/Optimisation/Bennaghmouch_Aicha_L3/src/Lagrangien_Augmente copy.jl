@doc doc"""
#### Objet

Résolution des problèmes de minimisation avec une contrainte d'égalité scalaire par l'algorithme du lagrangien augmenté.

#### Syntaxe
```julia
xmin,fxmin,flag,iter,muks,lambdaks = Lagrangien_Augmente(algo,f,gradf,hessf,c,gradc,hessc,x0,options)
```

#### Entrées
  - algo : (String) l'algorithme sans contraintes à utiliser:
    - "newton"  : pour l'algorithme de Newton
    - "cauchy"  : pour le pas de Cauchy
    - "gct"     : pour le gradient conjugué tronqué
  - f : (Function) la fonction à minimiser
  - gradf       : (Function) le gradient de la fonction
  - hessf       : (Function) la hessienne de la fonction
  - c     : (Function) la contrainte [x est dans le domaine des contraintes ssi ``c(x)=0``]
  - gradc : (Function) le gradient de la contrainte
  - hessc : (Function) la hessienne de la contrainte
  - x0 : (Array{Float,1}) la première composante du point de départ du Lagrangien
  - options : (Array{Float,1})
    1. epsilon     : utilisé dans les critères d'arrêt
    2. tol         : la tolérance utilisée dans les critères d'arrêt
    3. itermax     : nombre maximal d'itération dans la boucle principale
    4. lambda0     : la deuxième composante du point de départ du Lagrangien
    5. mu0, tho    : valeurs initiales des variables de l'algorithme

#### Sorties
- xmin : (Array{Float,1}) une approximation de la solution du problème avec contraintes
- fxmin : (Float) ``f(x_{min})``
- flag : (Integer) indicateur du déroulement de l'algorithme
   - 0    : convergence
   - 1    : nombre maximal d'itération atteint
   - (-1) : une erreur s'est produite
- niters : (Integer) nombre d'itérations réalisées
- muks : (Array{Float64,1}) tableau des valeurs prises par mu_k au cours de l'exécution
- lambdaks : (Array{Float64,1}) tableau des valeurs prises par lambda_k au cours de l'exécution

#### Exemple d'appel
```julia
using LinearAlgebra
algo = "gct" # ou newton|gct
f(x)=100*(x[2]-x[1]^2)^2+(1-x[1])^2
gradf(x)=[-400*x[1]*(x[2]-x[1]^2)-2*(1-x[1]) ; 200*(x[2]-x[1]^2)]
hessf(x)=[-400*(x[2]-3*x[1]^2)+2  -400*x[1];-400*x[1]  200]
c(x) =  (x[1]^2) + (x[2]^2) -1.5
gradc(x) = [2*x[1] ;2*x[2]]
hessc(x) = [2 0;0 2]
x0 = [1; 0]
options = []
xmin,fxmin,flag,iter,muks,lambdaks = Lagrangien_Augmente(algo,f,gradf,hessf,c,gradc,hessc,x0,options)
```

#### Tolérances des algorithmes appelés

Pour les tolérances définies dans les algorithmes appelés (Newton et régions de confiance), prendre les tolérances par défaut définies dans ces algorithmes.

"""
function Lagrangien_Augmente(algo, fonc::Function, contrainte::Function, gradfonc::Function,
  hessfonc::Function, grad_contrainte::Function, hess_contrainte::Function, x0, options)

  if options == []
    epsilon = 1e-2
    tol = 1e-5
    itermax = 1000
    lambda0 = 2
    mu0 = 100
    tho = 2
  else
    epsilon = options[1]
    tol = options[2]
    itermax = options[3]
    lambda0 = options[4]
    mu0 = options[5]
    tho = options[6]
  end

  n = length(x0)
  xmin = zeros(n)
  fxmin = 0
  flag = 0
  iter = 0
  muk = mu0
  muks = [mu0]
  lambdak = lambda0
  lambdaks = [lambda0]

  k = 0
  beta = 0.9
  eta = 0.1258925
  alpha = 0.1
  eps0 = 1 / mu0
  eta0 = eta / mu0^alpha
  arret = false

  xk = x0
  etak = eta0
  epsk = eps0

  xk_1 = x0
  etak_1 = eta0
  espk_1 = eps0
  lambdak_1 = lambda0
  muk_1 = muk

  while !arret
    xk = xk_1
    etak = etak_1
    epsk = espk_1
    lambdak = lambdak_1
    muk = muk_1
    # Fonction à minimiser 
    LA(x) = fonc(x) + lambdak' * contrainte(x) + (muk / 2) * (norm(contrainte(x)))^2
    # Calcul du gradient
    gradLA(x) = gradfonc(x) + lambdak' * grad_contrainte(x) + muk * grad_contrainte(x) * contrainte(x)
    # calcul de la hessienne : 
    hessLA(x) = hessfonc(x) + lambdak' * hess_contrainte(x) + muk * hess_contrainte(x) * contrainte(x) + muk * grad_contrainte(x) * grad_contrainte(x)'

    if algo == "newton"
      xk_1, ~ = Algorithme_De_Newton(LA, gradLA, hessLA, xk, [])
    elseif algo == "gct" || algo == "cauchy"
      xk_1, ~ = Regions_De_Confiance(algo, LA, gradLA, hessLA, xk, [])
    end

    grad_lagrangien(x, lambda) = gradfonc(x) + lambda' * grad_contrainte(x)
    # CN1 
    if norm(grad_lagrangien(xk_1, lambdak)) <= max(norm(grad_lagrangien(x0, lambda0)) * tol, tol)
      flag = 0
      break
    #elseif norm(contrainte(xk_1)) <= max(norm(contrainte(x0)) * tol, tol)
     # flag = 0
      #break
    end
    # Stagnation de l’itéré 
    # Stagnation de la fonction 

    #Mettre à jour (entre autres) les multiplicateurs
    if norm(contrainte(xk_1)) <= etak
      lambdak_1 = lambdak + muk * contrainte(xk_1)
      muk_1 = muk
      espk_1 = epsk / muk
      etak_1 = etak / (muk^beta)
      push!(muks,muk_1)
      push!(lambdaks,lambdak_1)
    else
      #  Autrement, mettre à jour (entre autres) le paramètre de pénalité
      lambdak_1 = lambdak
      muk_1 = muk * tho
      espk_1 = eps0 / muk_1
      etak = eta / (muk_1^alpha)
      push!(muks,muk_1)
      push!(lambdaks,lambdak_1)
    end
    k = k + 1
    # Nb d’itérations max
    if k == itermax 
      flag = 3
      break
    end
  end
  xmin = xk_1
  fxmin = fonc(xmin)
  return xmin, fxmin, flag, iter, muks, lambdaks
end
