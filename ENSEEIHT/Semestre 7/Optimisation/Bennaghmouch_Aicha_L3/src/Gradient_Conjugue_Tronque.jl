@doc doc"""
#### Objet
Cette fonction calcule une solution approchée du problème

```math
\min_{||s||< \Delta}  q(s) = s^{t} g + \frac{1}{2} s^{t}Hs
```

par l'algorithme du gradient conjugué tronqué

#### Syntaxe
```julia
s = Gradient_Conjugue_Tronque(g,H,option)
```

#### Entrées :   
   - g : (Array{Float,1}) un vecteur de ``\mathbb{R}^n``
   - H : (Array{Float,2}) une matrice symétrique de ``\mathbb{R}^{n\times n}``
   - options          : (Array{Float,1})
      - delta    : le rayon de la région de confiance
      - max_iter : le nombre maximal d'iterations
      - tol      : la tolérance pour la condition d'arrêt sur le gradient

#### Sorties:
   - s : (Array{Float,1}) le pas s qui approche la solution du problème : ``min_{||s||< \Delta} q(s)``

#### Exemple d'appel:
```julia
gradf(x)=[-400*x[1]*(x[2]-x[1]^2)-2*(1-x[1]) ; 200*(x[2]-x[1]^2)]
hessf(x)=[-400*(x[2]-3*x[1]^2)+2  -400*x[1];-400*x[1]  200]
xk = [1; 0]
options = []
s = Gradient_Conjugue_Tronque(gradf(xk),hessf(xk),options)
```
"""
function Gradient_Conjugue_Tronque(g, H, options)

    "# Si option est vide on initialise les 3 paramètres par défaut"
    if options == []
        delta = 2
        max_iter = 100
        tol = 1e-6
    else
        delta = options[1]
        max_iter = options[2]
        tol = options[3]
    end

    n = length(g)
    s = zeros(n)

    j = 0
    p0 = -g
    g0 = g

    gj = g0
    pj = p0
    sj = s

    gj_1 = gj
    pj_1 = pj
    sj_1 = sj

    #function sol(p,s,deltafct)
    #a = norm(p)^2
    #b = 2*dot(s,p)
    #c = (norm(s)^2)-(deltafct^2)
    #d = sqrt(b^2 - 4 *a*c)

    #if d > 0
    #  sol1 = (- b + sqrt(d)) / (2*a)
    #  sol2 = (- b - sqrt(d)) / (2*a)
    #  q1 = q(s + sol1*p)
    #  q2 = q(s + sol2*p)
    #  if q1 < q2
    #   sol = sol1
    #else 
    # sol = sol2
    #end
    #else
    #   sol= - b / (2*a)
    #end 
    #return sol
    #end 

    while ((j < 2 * n) && norm(gj) > max(tol * norm(g0), tol))

        kj = pj' * H * pj
        #kj = kj[1]

        q(x) = g' * x + 0.5 * x' * H * x

        if (kj <= 0)
            a = norm(pj)^2
            b = 2 * sj' * pj
            c = (norm(sj)^2) - (delta^2)
            d = b^2 - 4 * a * c
            sol1 = (-b + sqrt(d)) / (2 * a)
            sol2 = (-b - sqrt(d)) / (2 * a)
            q1 = q(sj + sol1 * pj)
            q2 = q(sj + sol2 * pj)
            if q1 < q2
                sol = sol1
            else
                sol = sol2
            end
            s = sj + (sol * pj)
            return s
        end

        alphaj = (gj' * gj) / kj

        if (norm(sj + alphaj * pj) >= delta)
            a = norm(pj)^2
            b = 2 * sj' * pj
            c = (norm(sj)^2) - (delta^2)
            d = b^2 - 4 * a * c
            if d > 0
                sol1 = (-b + sqrt(d)) / (2 * a)
                sol2 = (-b - sqrt(d)) / (2 * a)

                if sol1 > 0
                    sol = sol1
                elseif sol2 > 0
                    sol = sol2
                end
            else
                sol = -b / (2*a)
            end
            s = sj + (sol * pj)
            return s
        end


        # if d > 0
        #sol1 = (- b + sqrt(d)) / (2*a)
        #sol2 = (- b - sqrt(d)) / (2*a)
        #sol = max(sol1,sol2)
        #else
        #sol= - b / (2*a) 
        #end
        #s = sj + (sol * pj)
        #return s
        #end


        sj_1 = sj + alphaj * pj
        gj_1 = gj + alphaj * H * pj
        betaj = (gj_1' * gj_1) / (gj' * gj)
        pj_1 = -gj_1 + (betaj * pj)

        j = j + 1
        gj = gj_1
        sj = sj_1
        pj = pj_1

    end
    s=sj
    return s
end
