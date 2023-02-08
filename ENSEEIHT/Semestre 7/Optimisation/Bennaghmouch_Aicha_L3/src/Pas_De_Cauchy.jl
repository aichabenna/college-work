@doc doc"""
#### Objet
Cette fonction calcule une solution approchée du problème
```math
\min_{||s||< \Delta} s^{t}g + \frac{1}{2}s^{t}Hs
```
par le calcul du pas de Cauchy.

#### Syntaxe
```julia
s, e = Pas_De_Cauchy(g,H,delta)
```

#### Entrées
 - g : (Array{Float,1}) un vecteur de ``\mathbb{R}^n``
 - H : (Array{Float,2}) une matrice symétrique de ``\mathbb{R}^{n\times n}``
 - delta  : (Float) le rayon de la région de confiance

#### Sorties
 - s : (Array{Float,1}) une approximation de la solution du sous-problème
 - e : (Integer) indice indiquant l'état de sortie:
        si g != 0
            si on ne sature pas la boule
              e <- 1
            sinon
              e <- -1
        sinon
            e <- 0

#### Exemple d'appel
```julia
g = [0; 0]
H = [7 0 ; 0 2]
delta = 1
s, e = Pas_De_Cauchy(g,H,delta)
```
"""
function Pas_De_Cauchy(g,H,delta)

    e = 0
    n = length(g)
    s = zeros(n)

    # Resolution de min phi(t)
    ###########################################
    # phi(t) = q(-t*g) = 0.5*a*t^2 + b t + c
    a = g'*H*g
    b = - norm(g)^2
    # c = f(xk)
    # gradient(phi(t)) = a*t + b
    # Solution gradient(phi(t)) = 0 => t = -b/a

    if g != zeros(n)
      if a > 0 
        t = -b / a
        s = - t * g
        if norm(s) >= delta
          s = - delta * g/norm(g)
        end
      else
        s = - delta * g/norm(g)
      end

      if  norm(s) < delta # on ne staure pas la boule
        e = 1
      else
        e = -1
      end
    else
      e = 0
    end

    return s, e
end
