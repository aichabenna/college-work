function [beta, norm_grad_f_beta, f_beta, norm_delta, nb_it, exitflag] ...
          = Algo_Gauss_Newton(residu, J_residu, beta0, option)
%*****************************************************************
% Fichier  ~gergaud/ENS/Optim1a/TP-optim-20-21/TP-ref/GN_ref.m   *
% Novembre 2020                                                  *
% Université de Toulouse, INP-ENSEEIHT                           *
%*****************************************************************
%
% GN resout par l'algorithme de Gauss-Newton les problemes aux moindres carres
% Min 0.5||r(beta)||^2
% beta \in \IR^p
%
% Paramètres en entrés
% --------------------
% residu : fonction qui code les résidus
%          r : \IR^p --> \IR^n
% J_residu : fonction qui code la matrice jacobienne
%            Jr : \IR^p --> real(n,p)
% beta0 : point de départ
%         real(p)
% option(1) : Tol_abs, tolérance absolue
%             real
% option(2) : Tol_rel, tolérance relative
%             real
% option(3) : n_itmax, nombre d'itérations maximum
%             integer
%
% Paramètres en sortie
% --------------------
% beta      : beta
%             real(p)
% norm_gradf_beta : ||gradient f(beta)||
%                   real
% f_beta : f(beta)
%          real
% r_beta : r(beta)
%          real(n)
% norm_delta : ||delta||
%              real
% nbit : nombre d'itérations
%        integer
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
    res_beta= residu(beta);
    J_res_beta= J_residu(beta);
    grad_f_beta= J_res_beta' *res_beta;
    norm_grad_f_beta = norm(grad_f_beta);
    f_beta = 0.5*(res_beta)'*res_beta;
    seuil1 = max(Tol_rel*grad_f_beta, Tol_abs);
    while (~exitflag) 
        %mettre à jour seuil2 et seuil3
        seuil2 = max(Tol_rel*abs(f_beta), Tol_abs);
        seuil3= max(Tol_rel*norm(beta), Tol_abs);
        %mettre à jour beta
        delta= -(J_res_beta'*J_res_beta)\grad_f_beta;
        beta=beta+delta;
        % Calcul 
        % Condition 1 -> exitflag = 1
        res_beta=residu(beta);
        J_res_beta=J_residu(beta);
        grad_f_beta=J_res_beta'*res_beta;
        norm_grad_f_beta=norm(grad_f_beta);
        % Condition 2 -> exitflag = 2
        f_beta_plus = 0.5*(res_beta)'*res_beta;
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
