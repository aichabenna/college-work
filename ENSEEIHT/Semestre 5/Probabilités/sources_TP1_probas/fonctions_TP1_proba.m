
% TP1 de Probabilites : fonctions a completer et rendre sur Moodle
% Nom :
% Prénom : 
% Groupe : 1SN-

function varargout = fonctions_TP1_proba(varargin)

    switch varargin{1}     
        case 'ecriture_RVB'
            varargout{1} = feval(varargin{1},varargin{2:end});
        case {'vectorisation_par_colonne','decorrelation_colonnes'}
            [varargout{1},varargout{2}] = feval(varargin{1},varargin{2:end});
        case 'calcul_parametres_correlation'
            [varargout{1},varargout{2},varargout{3}] = feval(varargin{1},varargin{2:end}); 
    end

end

% Fonction ecriture_RVB (exercice_0.m) ------------------------------------
% (Copiez le corps de la fonction ecriture_RVB du fichier du meme nom)
function image_RVB = ecriture_RVB(image_originale)
canalR = image_originale(1:2:end, 2:2:end);
canalB = image_originale(2:2:end, 1:2:end);
canalV1 = image_originale(1:2:end, 1:2:end);
canalV2 = image_originale(2:2:end, 2:2:end);
canalV = (canalV1 + canalV2)/2;
image_RVB = cat(3, canalR, canalV, canalB);
end

% Fonction vectorisation_par_colonne (exercice_1.m) -----------------------
function [Vd,Vg] = vectorisation_par_colonne(I)
IVg= I(:, 1:end-1);
IVd= I(:, 2:end);
Vd= IVd(:);
Vg= IVg(:);
end

% Fonction calcul_parametres_correlation (exercice_1.m) -------------------
function [r,a,b] = calcul_parametres_correlation(Vd,Vg)
Vd_moy= mean(Vd);
Vg_moy= mean(Vg);
diff_Vd= Vd - Vd_moy;
diff_Vg= Vg - Vg_moy;
tmp_Vd = mean(diff_Vd.^2);
tmp_Vg = mean(diff_Vg.^2);
cov_Vd = sqrt(tmp_Vd) ;
cov_Vg = sqrt(tmp_Vg) ;
cov_Vd_Vg = mean(diff_Vd .* diff_Vg);

r = cov_Vd_Vg/(cov_Vd*cov_Vg);

a = cov_Vd_Vg/tmp_Vd;
b = -a * Vd_moy+ Vg_moy;
end

% Fonction decorrelation_colonnes (exercice_2.m) --------------------------
function [I_decorrelee,I_min] = decorrelation_colonnes(I,I_max)
    I_decorrelee=I;
    [row, column]= size(I);
    for j = 2:column
        for i = 1:row
            I_decorrelee(i,j) = I_decorrelee(i,j) - I(i,j-1);
        end
    end
    I_min= - I_max;
    % autre méthode :
    % I_decorrelee = [I(:,1), I(:, 2:end) - I(:, 1:end-1)];
end



