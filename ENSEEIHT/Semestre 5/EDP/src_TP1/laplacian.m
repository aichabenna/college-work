function L = laplacian(nu,dx1,dx2,N1,N2)
%
%  Cette fonction construit la matrice de l'opérateur Laplacien 2D anisotrope
%
%  Inputs
%  ------
%
%  nu : nu=[nu1;nu2], coefficients de diffusivité dans les dierctions x1 et x2. 
%
%  dx1 : pas d'espace dans la direction x1.
%
%  dx2 : pas d'espace dans la direction x2.
%
%  N1 : nombre de points de grille dans la direction x1.
%
%  N2 : nombre de points de grilles dans la direction x2.
%
%  Outputs:
%  -------
%
%  L      : Matrice de l'opérateur Laplacien (dimension N1N2 x N1N2)
%
% 

% Initialisation
%pour faire une marice creuse
L = sparse(N1*N2, N1*N2);
%%%%%%%%%%%%%%%%%%%%%%
%%%%%% TO DO %%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%
coeff =(- nu(2)/ (dx2^2));
V_p1 = [0; coeff * ones(N2 - 1, 1)];
V_m1 = [coeff* ones(N2 - 1, 1); 0];

V_1= repmat(V_m1, N1, 1);
V_plus_1 = repmat(V_p1, N1, 1);
% ou directement 
% circshift(V_1,1);
% flipud(V_1);

L = spdiags(V_1,-1, L);
L = spdiags(V_plus_1,1, L);

Bin = ones(N1*N2,1) * ( 2*((nu(1)/ (dx1^2))+ (nu(2)/ (dx2^2))) );
L = spdiags(Bin,0, L);

Bin = ones((N1*N2)/2,1) * (- nu(1)/ (dx1^2));
L = spdiags(Bin,N2, L);
L = spdiags(Bin,-N2, L);

end    
