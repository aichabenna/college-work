function [Vd,Vg] = vectorisation_par_colonnes(I)
IVd= I(:, 1:end-1);
IVg= I(:, 2:end);
Vd= IVd(:);
Vg= IVg(:);
end