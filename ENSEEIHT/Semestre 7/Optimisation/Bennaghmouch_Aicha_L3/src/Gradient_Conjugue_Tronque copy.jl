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
    g0 = g
    s0 = zeros(n)
    p0 = -g

    gj = g0
    sj = s0
    pj = p0

    gj_1 = g0
    sj_1 = s0
    pj_1 = p0
    # CN1
    while j < 2 * n && norm(gj) > max(norm(g0) * tol, tol)

        kj = pj' * H * pj
        if kj <= 0
            # la racine de ∥sj + σpj∥ = ∆ pour laquelle q(sj + σpj ) est la plus petite
            a = norm(pj)^2
            b = 2 * dot(sj,pj)
            c = norm(sj)^2 - delta^2
            d = b^2 - 4 * a * c
            if d > 0
                sigma1 = (-b + sqrt(d)) / (2 * a)
                sigma2 = (-b - sqrt(d)) / (2 * a)
                # q(sigma)
                t1 = sj + sigma1 * pj
                t2 = sj + sigma2 * pj
                q_t1 = g' * t1 + 0.5 * t1' * H * t1
                q_t2 = g' * t2 + 0.5 * t2' * H * t2
                if q_t1 < q_t2
                    sigma_j = sigma1
                else
                    sigma_j = sigma2
                end
            else
                sigma_j = -b / (2 * a)
            end
            return sj + sigma_j * pj
        end

        alpha_j = gj' * gj / kj
        t = sj + alpha_j * pj
        if norm(t) >= delta
            # la racine positive de ∥sj + σpj∥ = ∆
            a = norm(pj)^2
            b = 2 * dot(sj,pj)
            c = norm(sj)^2 - delta^2
            d = b^2 - 4 * a * c
            if d > 0
                sigma1 = (-b + sqrt(d)) / (2 * a)
                sigma2 = (-b - sqrt(d)) / (2 * a)
                if sigma1 > 0
                    sigma_j = sigma1
                elseif sigma2 > 0
                    sigma_j = sigma2
                end
            else
                sigma_j = -b / (2 * a)
            end
            return sj + sigma_j * pj
        end

        sj_1 = sj + alpha_j * pj
        gj_1 = gj + alpha_j * H * pj
        beta_j = (gj_1' * gj_1) / (gj' * gj)
        pj_1 = -gj_1 + beta_j * pj
        j = j + 1
        gj = gj_1
        sj = sj_1
        pj = pj_1

    end
    s = sj
    return s
end
