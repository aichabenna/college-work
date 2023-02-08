
% TP3 de Statistiques : fonctions a completer et rendre sur Moodle
% Nom : Bennaghmouch
% Prenom : Aicha
% Groupe : 1SN-D

function varargout = fonctions_TP3_stat(varargin)

    [varargout{1},varargout{2}] = feval(varargin{1},varargin{2:end});

end

% Fonction estimation_F (exercice_1.m) ------------------------------------
function [rho_F,theta_F,ecart_moyen] = estimation_F(rho,theta)
    A= [cos(theta) sin(theta)];
    B= rho;
    X= A\B;
    rho_F = sqrt(X(1)^2 + X(2)^2);
    theta_F= atan2(X(2), X(1));
    % A modifier lors de l'utilisation de l'algorithme RANSAC (exercice 2)
    ecart = rho - rho_F * cos(theta - theta_F);
    ecart_moyen = mean(ecart);

end

% Fonction RANSAC_2 (exercice_2.m) ----------------------------------------
function [rho_F_estime,theta_F_estime] = RANSAC_2(rho,theta,parametres)
    n = length(theta);

    S1 = parametres(1);
    S2 = parametres(2);
    K_max = parametres(3);
    meilleur_ecart_moyen=Inf;
    
    for i = 1:K_max
        % Tirer 2 droites
        indices = randperm(n,2);
        % Estimer Fa de ces deux droites
        [rho_Fa,theta_Fa,~] = estimation_F(rho(indices),theta(indices));
        % d(Dk, Fa) < S1
        Droites_conformes = abs(rho -rho_Fa *cos(theta-theta_Fa))<=S1;
        % Combien de droites sont assez proches
        % Si #Dproches/#D > 2
        if sum(Droites_conformes) / length(rho) > S2
            % estimer Fb avec les droites proches + ecart moyen
            [rho_Fb,theta_Fb,ecart_moyen] = estimation_F(rho(Droites_conformes),theta(Droites_conformes));
            if ecart_moyen < meilleur_ecart_moyen 
                meilleur_ecart_moyen = ecart_moyen;     
                rho_F_estime =rho_Fb;
                theta_F_estime =theta_Fb;
            end
        end
    end
end

% Fonction G_et_R_moyen (exercice_3.m, bonus, fonction du TP1) ------------
function [G, R_moyen, distances] = ...
         G_et_R_moyen(x_donnees_bruitees,y_donnees_bruitees)
     xG = mean (x_donnees_bruitees) ;
     yG = mean (y_donnees_bruitees) ;
     G = [xG yG];
     distances = sqrt(( x_donnees_bruitees - xG).^2 + (y_donnees_bruitees - yG).^2);
     R_moyen = mean(distances);
end

% Fonction estimation_C_et_R (exercice_3.m, bonus, fonction du TP1) -------
function [C_estime,R_estime,critere] = ...
         estimation_C_et_R(x_donnees_bruitees,y_donnees_bruitees,n_tests,C_tests,R_tests)
     
    % Attention : par rapport au TP1, le tirage des C_tests et R_tests est 
    %             considere comme etant deje effectue 
    %             (il doit etre fait au debut de la fonction RANSAC_3)
    
    [G, R_moyen, ~] = G_et_R_moyen(x_donnees_bruitees,y_donnees_bruitees);
    %C_tests = rand(n_tests, 2);
    C = G + ((C_tests - 0.5) .* (2*R_moyen));
    %R_tests = rand(n_tests, 1);
    R = (R_tests+0.5) .* R_moyen ;

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

    critere = Inf;

end

% Fonction RANSAC_3 (exercice_3, bonus) -----------------------------------
function [C_estime,R_estime] = ...
         RANSAC_3(x_donnees_bruitees,y_donnees_bruitees,parametres)
     
    % Attention : il faut faire les tirages de C_tests et R_tests ici
    n = length(theta);

    S1 = parametres(1);
    S2 = parametres(2);
    K_max = parametres(3);
    n_tests = parametres(4);
    meilleur_ecart_moyen=Inf;

    for i = 1:K_max
        % Tirer 3 pts
        indices = randperm(n,3);
        x = [ x_donnees_bruitees(indices(1)) x_donnees_bruitees(indices(2)) x_donnees_bruitees(indices(3))];
        y = [ y_donnees_bruitees(indices(1)) y_donnees_bruitees(indices(2)) y_donnees_bruitees(indices(3))];

        [C_tests,R_tests] = cercle_3_points(x,y);
        % Estimer Fa de ces deux droites
        [C_estime,R_estime,critere]= estimation_C_et_R(x_donnees_bruitees,y_donnees_bruitees,n_tests,C_tests,R_tests);        % d(Dk, Fa) < S1
       
        Droites_conformes = abs(rho -rho_Fa *cos(theta-theta_Fa))<=S1;
        % Combien de droites sont assez proches
        % Si #Dproches/#D > 2
        if sum(Droites_conformes) / n > S2
            C_tests = G + ((C_tests - 0.5) .* (2*R_moyen));
            R_tests = (R_tests+0.5) .* R_moyen ;
            % estimer Fb avec les droites proches + ecart moyen
            [C_estime,R_estime,critere]= estimation_C_et_R(x_donnees_bruitees,y_donnees_bruitees,n_tests,C_tests,R_tests)            
            if critere < meilleur_ecart_moyen 
                meilleur_ecart_moyen = critere;     
                C_estime =C_tests;
                R_estime =R_tests;
            end
        end
    end


end
