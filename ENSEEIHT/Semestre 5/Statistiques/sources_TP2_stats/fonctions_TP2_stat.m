
% TP2 de Statistiques : fonctions a completer et rendre sur Moodle
% Nom : Bennaghmouch
% Prénom : Aicha
% Groupe : 1SN-D

function varargout = fonctions_TP2_stat(varargin)
    [varargout{1},varargout{2}] = feval(varargin{1},varargin{2:end});
end

% Fonction centrage_des_donnees (exercice_1.m) ----------------------------
function [x_G, y_G, x_donnees_bruitees_centrees, y_donnees_bruitees_centrees] = ...
                centrage_des_donnees(x_donnees_bruitees,y_donnees_bruitees)

     x_G = mean (x_donnees_bruitees) ;
     y_G = mean (y_donnees_bruitees) ;
     x_donnees_bruitees_centrees = x_donnees_bruitees - x_G;
     y_donnees_bruitees_centrees = y_donnees_bruitees - y_G;

end

% Fonction estimation_Dyx_MV (exercice_1.m) -------------------------------
function [a_Dyx,b_Dyx] = ...
           estimation_Dyx_MV(x_donnees_bruitees,y_donnees_bruitees,n_tests)
     [x_G, y_G, xi, yi] = centrage_des_donnees(x_donnees_bruitees,y_donnees_bruitees)
     phi = (rand(n_tests,1) -0.5)*pi;
     phiM = repmat(phi, 1, length(xi));
     X = repmat(xi , n_tests, 1);
     Y = repmat(yi , n_tests, 1);
     A_sommer = (Y - tan(phiM) .* X).^2;
     somme = sum(A_sommer,2);
     [~, ind] = min (somme);
     a_Dyx = phiM (ind);
     b_Dyx = y_G - a_Dyx * x_G;
end

% Fonction estimation_Dyx_MC (exercice_2.m) -------------------------------
function [a_Dyx,b_Dyx] = ...
                   estimation_Dyx_MC(x_donnees_bruitees,y_donnees_bruitees)
    n = length(x_donnees_bruitees);
    A= [x_donnees_bruitees' ones(n,1)]
    B= y_donnees_bruitees';
    % X_etoile = (A' * B)\ (A' *A);
    X_etoile = A\B;
    a_Dyx = X_etoile(1);
    b_Dyx = X_etoile(2);

end

% Fonction estimation_Dorth_MV (exercice_3.m) -----------------------------
function [theta_Dorth,rho_Dorth] = ...
         estimation_Dorth_MV(x_donnees_bruitees,y_donnees_bruitees,n_tests)
    
    [x_G, y_G, xi, yi] = centrage_des_donnees(x_donnees_bruitees,y_donnees_bruitees)
    theta = (rand(n_tests,1)) *pi;
    A_sommer = (cos(theta)*xi + sin(theta)* yi).^2;
    somme = sum(A_sommer,2);
    [~, ind] = min (somme);

    theta_Dorth = theta (ind);
    rho_Dorth = y_G* sin(theta_Dorth) +cos(theta_Dorth) * x_G;

    if rho_Dorth <0 
        rho_Dorth = - rho_Dorth;
        theta_Dorth = theta_Dorth - pi;
    end
end

% Fonction estimation_Dorth_MC (exercice_4.m) -----------------------------
function [theta_Dorth,rho_Dorth] = ...
                 estimation_Dorth_MC(x_donnees_bruitees,y_donnees_bruitees)
    [x_G, y_G, xi, yi] = centrage_des_donnees(x_donnees_bruitees,y_donnees_bruitees)
    C= cat(1,xi,yi);
    [V, D] = eig(C'*C);
    [lamdamin, ind ] = min(diag(D));
    vpmin = V(:,ind);
    Y= vpmin;
    theta_Dorth = atan2(Y(2), Y(1));
    rho_Dorth = y_G* sin(theta_Dorth) +cos(theta_Dorth) * x_G;

end
