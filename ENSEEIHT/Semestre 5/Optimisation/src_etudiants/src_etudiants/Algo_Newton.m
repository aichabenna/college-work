function [beta, norm_grad_f_beta, f_beta, norm_delta, nb_it, exitflag] ...
          = Algo_Newton(Hess_f_C14, beta0, option)
%************************************************************
% Fichier  ~gergaud/ENS/Optim1a/TP-optim-20-21/Newton_ref.m *
% Novembre 2020                                             *
% Université de Toulouse, INP-ENSEEIHT                      *
%************************************************************
%
% Newton r�sout par l'algorithme de Newton les problemes aux moindres carres
% Min 0.5||r(beta)||^2
% beta \in R^p
%
% Parametres en entrees
% --------------------
% Hess_f_C14 : fonction qui code la hessiennne de f
%              Hess_f_C14 : R^p --> matrice (p,p)
%              (la fonction retourne aussi le residu et la jacobienne)
% beta0  : point de départ
%          real(p)
% option(1) : Tol_abs, tolérance absolue
%             real
% option(2) : Tol_rel, tolérance relative
%             real
% option(3) : nitimax, nombre d'itérations maximum
%             integer
%
% Parametres en sortie
% --------------------
% beta      : beta
%             real(p)
% norm_gradf_beta : ||gradient f(beta)||
%                   real
% f_beta    : f(beta)
%             real
% res       : r(beta)
%             real(n)
% norm_delta : ||delta||
%              real
% nbit       : nombre d'itérations
%              integer
% exitflag   : indicateur de sortie
%              integer entre 1 et 4
% exitflag = 1 : ||gradient f(beta)|| < max(Tol_rel||gradient f(beta0)||,Tol_abs)
% exitflag = 2 : |f(beta^{k+1})-f(beta^k)| < max(Tol_rel|f(beta^k)|,Tol_abs)
% exitflag = 3 : ||delta)|| < max(Tol_rel delta^k),Tol_abs)
% exitflag = 4 : nombre maximum d'itérations atteint
%      
% ---------------------------------------------------------------------------------

% TO DO %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

    beta = beta0;
    Tol_abs= option(1);
    Tol_rel= option(2);
    n_itmax= option(3);
    nb_it = 0;
    exitflag = 0;
    [Hf, res_beta, J_res_beta]= Hess_f_C14(beta);
    grad_f_beta= J_res_beta' *res_beta;
    norm_grad_f_beta = norm(grad_f_beta);
    f_beta = 0.5*(res_beta)'*res_beta;
    seuil1 = max(Tol_rel*grad_f_beta, Tol_abs);
    while (~exitflag) 
        %mettre � jour seuil2 et seuil3
        seuil2 = max(Tol_rel*abs(f_beta), Tol_abs);
        seuil3= max(Tol_rel*norm(beta), Tol_abs);
        %mettre � jour beta
        delta= -Hf\grad_f_beta;
        beta=beta+delta;

        % Calcul 
        % Condition 1 -> exitflag = 1
        [Hf, res_beta, J_res_beta]= Hess_f_C14(beta);
        grad_f_beta=J_res_beta'*res_beta;
        norm_grad_f_beta=norm(grad_f_beta);
        % Condition 2 -> exitflag = 2
        f_beta_plus = 0.5*(res_beta')*res_beta;
        delta_f=f_beta_plus - f_beta;
        f_beta=f_beta_plus;
        % Condition 3 -> exitflag = 3
        norm_delta= norm(delta);
        % Condition 4 -> exitflag = 4
        nb_it=nb_it+1;

        % Test 
        % Condition 1 -> exitflag = 1
        if (norm_grad_f_beta<seuil1)
            exitflag=1;
        elseif (abs(delta_f)<seuil2)
            exitflag=2;
        elseif (norm_delta<seuil3)
            exitflag=3;
        elseif (nb_it == n_itmax)
            exitflag=4;
        end

    end    
end
