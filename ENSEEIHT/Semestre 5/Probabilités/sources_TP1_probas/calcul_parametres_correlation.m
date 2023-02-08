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