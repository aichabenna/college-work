function [I_decorrelee,I_min] = decorrelation_colonnes(I,I_max)
    I_decorrelee=repmat(I,1);
    [row, column]= size(I);
    for j = 2:column
        for i = 1:row
            I_decorrelee(i,j) = I_decorrelee(i,j) - I_decorrelee(i,j-1);
        end
    end
    I_min= min(min(I_max));
end