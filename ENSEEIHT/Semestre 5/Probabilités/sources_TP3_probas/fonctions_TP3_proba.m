
% TP3 de Probabilites : fonctions a completer et rendre sur Moodle
% Nom : Bennaghmouch
% Prénom : Aicha
% Groupe : 1SN-D

function varargout = fonctions_TP3_proba(varargin)

    switch varargin{1}
        
        case 'matrice_inertie'
            
            [varargout{1},varargout{2}] = feval(varargin{1},varargin{2:end});
            
        case {'ensemble_E_recursif','calcul_proba'}
            
            [varargout{1},varargout{2},varargout{3}] = feval(varargin{1},varargin{2:end});
    
    end
end

% Fonction ensemble_E_recursif (exercie_1.m) ------------------------------
function [E,contour,G_somme] = ...
    ensemble_E_recursif(E,contour,G_somme,i,j,voisins,G_x,G_y,card_max,cos_alpha)
    contour(i,j)=0;
    k=1;
    while k<=8 && size(E,1)<card_max
        voisin_i= i+voisins(k,1);
        voisin_j=j+voisins(k,2);
        if contour(voisin_i, voisin_j)~=0
            Gv= [G_x(voisin_i, voisin_j) G_y(voisin_i,voisin_j)];
            norm_Gv= norm(Gv);
            norm_G_somme= norm(G_somme);
            if (G_somme/norm_G_somme) * (Gv/norm_Gv)'> cos_alpha
                E=[E; voisin_i voisin_j];
                G_somme=G_somme+Gv;
                [E, contour, G_somme]=ensemble_E_recursif(E,contour,G_somme,voisin_i,voisin_j,voisins,G_x,G_y,card_max,cos_alpha);
            end
        end
        k=k+1;
    end

end

% Fonction matrice_inertie (exercice_2.m) ---------------------------------
function [M_inertie,C] = matrice_inertie(E,G_norme_E)

    
    E_x= E(:, 2);
    E_y= E(:,1);
    E_x= E_x.*G_norme_E;
    G_x_somme= sum(E_x);
    E_y= E_y.*G_norme_E;
    G_y_somme= sum(E_y);
    G_norm_sum= sum(G_norme_E);
    x_barre= G_x_somme/G_norm_sum;
    y_barre= G_y_somme/G_norm_sum;
    C= [x_barre y_barre];

    E_x= E(:, 2);
    E_y= E(:,1);
    calcul_M11= G_norme_E.*((E_x-x_barre).^2);
    M11= sum(calcul_M11)/ G_norm_sum;
    calcul_M12= G_norme_E.*(E_x-x_barre).*(E_y-y_barre);
    M12= sum(calcul_M12)/ G_norm_sum;
    calcul_M22= G_norme_E.*((E_y-y_barre).^2);
    M22= sum(calcul_M22)/ G_norm_sum;

    M_inertie= [M11 M12; M12 M22];

end

% Fonction calcul_proba (exercice_2.m) ------------------------------------
function [x_min,x_max,probabilite] = calcul_proba(E_nouveau_repere,p)
    x_min= min(E_nouveau_repere(:,1));
    x_max= max(E_nouveau_repere(:,1));

    y_min= min(E_nouveau_repere(:,2));
    y_max= max(E_nouveau_repere(:,2));
    N= round((y_max-y_min)*(x_max-x_min));
    [n, ~ ]=size(E_nouveau_repere);
    probabilite=1- binocdf(n-1, N,p);
    
end
