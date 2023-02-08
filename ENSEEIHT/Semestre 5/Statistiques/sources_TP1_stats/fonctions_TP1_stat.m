
% TP1 de Statistiques : fonctions a completer et rendre sur Moodle
% Nom : Bennaghmouch
% Prénom : Aicha
% Groupe : 1SN-D

function varargout = fonctions_TP1_stat(varargin)

    [varargout{1},varargout{2}] = feval(varargin{1},varargin{2:end});

end

% Fonction G_et_R_moyen (exercice_1.m) ----------------------------------
function [G, R_moyen, distances] = ...
         G_et_R_moyen(x_donnees_bruitees,y_donnees_bruitees)

     %Pi = [x_donnees_bruitees y_donnees_bruitees];
     xG = mean (x_donnees_bruitees) ;
     yG = mean (y_donnees_bruitees) ;
     G = [xG yG];
     distances = sqrt(( x_donnees_bruitees - xG).^2 + (y_donnees_bruitees - yG).^2);
     R_moyen = mean(distances);
end

% Fonction estimation_C_uniforme (exercice_1.m) ---------------------------
function [C_estime, R_moyen] = ...
         estimation_C_uniforme(x_donnees_bruitees,y_donnees_bruitees,n_tests)
     [G, R_moyen, ~] = G_et_R_moyen(x_donnees_bruitees,y_donnees_bruitees);

     C_tests = rand(n_tests, 2);
     C = G + ((C_tests - 0.5) .* (2*R_moyen));

     X= repmat(x_donnees_bruitees, n_tests,1);
     Y= repmat(y_donnees_bruitees, n_tests, 1);

     Cx =repmat(C(:,1), 1, length(x_donnees_bruitees)); 
     Cy = repmat(C(:,2), 1, length(y_donnees_bruitees)); 

     d = sqrt(( X - Cx).^2 + (Y - Cy).^2);
     d_R = (d - R_moyen).^2
     somme= sum(d_R, 2);
     [~, i_min] = min(somme);
     C_estime = C(i_min, :);

end

% Fonction estimation_C_et_R_uniforme (exercice_2.m) ----------------------
function [C_estime, R_estime] = ...
         estimation_C_et_R_uniforme(x_donnees_bruitees,y_donnees_bruitees,n_tests)
    [G, R_moyen, ~] = G_et_R_moyen(x_donnees_bruitees,y_donnees_bruitees);
    C_tests = rand(n_tests, 2);
    C = G + ((C_tests - 0.5) .* (2*R_moyen));
    R_tests = rand(n_tests, 1);
    R = (R_tests-0.5) .* R_moyen + R_moyen;
    %R = (R_tests+0.5) .* R_moyen ;

    X= repmat(x_donnees_bruitees, n_tests,1);
    Y= repmat(y_donnees_bruitees, n_tests, 1);

    Cx =repmat(C(:,1), 1, length(x_donnees_bruitees)); 
    Cy = repmat(C(:,2), 1, length(y_donnees_bruitees)); 

    d_p_c = sqrt(( X - Cx).^2 + (Y - Cy).^2);
    d_p_c_r = (d_p_c - R).^2;

    somme = sum (d_p_c_r, 2);
    
    [~, i_min] = min(somme);
    C_estime = C(i_min, :);
    R_estime = R(i_min);
end

% Fonction occultation_donnees (donnees_occultees.m) ----------------------
function [x_donnees_bruitees, y_donnees_bruitees] = ...
         occultation_donnees(x_donnees_bruitees, y_donnees_bruitees, theta_donnees_bruitees)
    theta1 = rand * 2*pi;
    theta2 = rand * 2*pi ; 

    bool_theta_cond1 = theta_donnees_bruitees > theta1;
    bool_theta_cond2 = theta_donnees_bruitees< theta2;

    theta_conservees = bool_theta_cond2 & bool_theta_cond1;

    x_conservees = x_donnees_bruitees(theta_conservees);
    y_conservees = y_donnees_bruitees(theta_conservees);

    x_donnees_bruitees = x_conservees;
    y_donnees_bruitees = y_conservees;
end

% Fonction estimation_C_et_R_normale (exercice_4.m, bonus) ----------------
function [C_estime, R_estime] = ...
         estimation_C_et_R_normale(x_donnees_bruitees,y_donnees_bruitees,n_tests)



end
