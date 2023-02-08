
% TP2 de Probabilites : fonctions a completer et rendre sur Moodle
% Nom :
% Prenom : 
% Groupe : 1SN-

function varargout = fonctions_TP2_proba(varargin)

    switch varargin{1}
        
        case {'calcul_frequences_caracteres','determination_langue','coeff_compression','gain_compression','partitionnement_frequences'}

            varargout{1} = feval(varargin{1},varargin{2:end});
            
        case {'recuperation_caracteres_presents','tri_decroissant_frequences','codage_arithmetique'}
            
            [varargout{1},varargout{2}] = feval(varargin{1},varargin{2:end});
            
        case 'calcul_parametres_correlation'
            
            [varargout{1},varargout{2},varargout{3}] = feval(varargin{1},varargin{2:end});
            
    end

end

% Fonction calcul_frequences_caracteres (exercice_0.m) --------------------
function frequences = calcul_frequences_caracteres(texte,alphabet)
    frequences=zeros(size(alphabet));
    for i=1:length(texte) 
        for j=1:length(alphabet)
            if texte(i) == alphabet(j) 
                frequences(j)=frequences(j)+1;
            end
        end
    end
    %for i=1:length(alphabet)
        %frequences(i)=count(texte, alphabet(i));
    %end
    frequences=frequences./length(texte) ;
end

% Fonction recuperation_caracteres_presents (exercice_0.m) ----------------
function [selection_frequences,selection_alphabet] = ...
                      recuperation_caracteres_presents(frequences,alphabet)
    %Méthode 1:
    %indices= find(frequences>0);
    %selection_frequences= zeros(size(indices));
    %selection_alphabet= zeros(size(indices));
    %for i=1:length(indices)
    %   selection_frequences(i)=frequences(indices(i));
    %   selection_alphabet(i)=alphabet(indices(i));
    %end
    %Methode 2:
    %indices__freq_non_nulles= frequences>0;
    %selection_frequences=frequences(indices__freq_non_nulles);
    %selection_alphabet=alphabet(indices__freq_non_nulles);
    %Methode 3:
    selection_frequences=frequences(frequences>0);
    selection_alphabet=alphabet(frequences>0);
end

% Fonction tri_decremental_frequences (exercice_0.m) ----------------------
function [frequences_triees,indices_frequences_triees] = ...
                           tri_decroissant_frequences(selection_frequences)
    [frequences_triees,indices_frequences_triees]= sort(selection_frequences, 'descend');
end

% Fonction determination_langue (exercice_1.m) ----------------------------
function langue = determination_langue(frequences_texte, frequences_langue, nom_norme)
    % Note : la variable nom_norme peut valoir 'L1', 'L2' ou 'Linf'.
    freq=frequences_texte - frequences_langue;
    switch nom_norme
        case 'L1'
            freq=abs(freq);
            L= sum(freq,2);
        case 'L2'
            freq=freq.^2;
            L= sum(freq,2);
        otherwise
            L= max(freq,[],2);
    end
    [~,langue]= min(L);
end

% Fonction coeff_compression (exercice_2.m) -------------------------------
function coeff_comp = coeff_compression(signal_non_encode,signal_encode)
    coeff_comp=(length(signal_non_encode)*8)/length(signal_encode);
end

% Fonction coeff_compression (exercice_2bis.m) -------------------------------
function gain_comp = gain_compression(coeff_comp_avant,coeff_comp_apres)
    gain_comp=coeff_comp_apres/coeff_comp_avant;
end

% Fonction partitionnement_frequences (exercice_3.m) ----------------------
function bornes = partitionnement_frequences(selection_frequences)
    bornes=zeros(2,length(selection_frequences));
    bornes(2,1)=selection_frequences(1);
    for i = 2:length(selection_frequences)
        bornes(1,i)=bornes(2,i-1);
        bornes(2,i) = bornes(1,i)+selection_frequences(i) ;
    end
end

% Fonction codage_arithmetique (exercice_3.m) -----------------------------
function [borne_inf,borne_sup] = ...
                       codage_arithmetique(texte,selection_alphabet,bornes)
    borne_inf=0;
    borne_sup=1;
    for i=1:length(texte)
        largeur= borne_sup- borne_inf;
        j= find(selection_alphabet==texte(i));
        borne_sup=borne_inf+largeur*bornes(2,j);
        borne_inf=borne_inf+largeur*bornes(1,j);
    end
end