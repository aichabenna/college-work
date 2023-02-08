with Ada.Text_IO;          use Ada.Text_IO;
with Ada.Integer_Text_IO;  use Ada.Integer_Text_IO;

-- Auteur: 
-- Gérer un stock de matériel informatique.
--
package body Stocks_Materiel is

    procedure Creer (Stock : out T_Stock) is
    begin
        Stock.Nb_Materiels:=0;
    end Creer;


    function Nb_Materiels (Stock: in T_Stock) return Integer is
    begin
        return Stock.Nb_Materiels;
    end;


    procedure Enregistrer (
            Stock        : in out T_Stock;
            Numero_Serie : in     Integer;
            Nature       : in     T_Nature;
            Annee_Achat  : in     Integer
        ) is
    begin
        if Stock.Nb_Materiels < CAPACITE then -- Nb_Materiels(Stock)
            Stock.Nb_Materiels:=Stock.Nb_Materiels+1;
            Stock.Materiels(Stock.Nb_Materiels).Numero_Serie:=Numero_Serie;
            Stock.Materiels(Stock.Nb_Materiels).Nature:=Nature;
            Stock.Materiels(Stock.Nb_Materiels).Annee_Achat:=Annee_Achat;
            Stock.Materiels(Stock.Nb_Materiels).Etat:=True;
        end if;
    end;
    
    function Nb_Materiels_Hors_Fonctionnement (Stock: in T_Stock) return Integer is   
        Nb : Integer;
    begin
        Nb:=0;
        for Materiel in 1..(Stock.Nb_Materiels) loop
            if not Stock.Materiels(Materiel).Etat then 
                Nb:=Nb+1;
            end if;
        end loop;
        return Nb;
    end;
        
    procedure Mettre_A_Jour (Stock: in out T_Stock; Etat : in Boolean ; Numero_Serie : in Integer)is
    begin
        for i in 1..(Stock.Nb_Materiels) loop
            if Stock.Materiels(i).Numero_Serie = Numero_Serie then 
                Stock.Materiels(i).Etat := Etat;
            end if;
        end loop;
    end Mettre_A_Jour;
    

    procedure Supprimer_Material (Stock: in out T_Stock; Numero_Serie : in Integer) is
        Nb_Materiels: Integer;
        i: Integer;
    begin
        i:=1;
        Nb_Materiels:=Stock.Nb_Materiels;
        while i<= Nb_Materiels loop
            if Stock.Materiels(i).Numero_Serie = Numero_Serie then 
                for j in i..(Nb_Materiels-1) loop
                    Stock.Materiels(j).Numero_Serie:=Stock.Materiels(j+1).Numero_Serie;
                    Stock.Materiels(j).Nature:=Stock.Materiels(j+1).Nature;
                    Stock.Materiels(j).Annee_Achat:=Stock.Materiels(j+1).Annee_Achat;
                    Stock.Materiels(j).Etat:=Stock.Materiels(j+1).Etat;
                end loop;
                Stock.Nb_Materiels:=Stock.Nb_Materiels-1;
                Nb_Materiels:=Nb_Materiels-1;
            end if;
            i:=i+1;
        end loop;
        
    end Supprimer_Material;

    procedure Afficher (Stock: in T_Stock) is
    begin
        for i in 1..(Stock.Nb_Materiels) loop
            Put("Matériel ");
            Put(i,1);
            Put(" Numero de Serie : ");
            Put(Stock.Materiels(i).Numero_Serie,1);
            Put(" Nature : ");
            Put(T_Nature'Image((Stock.Materiels(i).Nature)));
            Put(" Année d'achat : ");
            Put(Stock.Materiels(i).Annee_Achat,1);
            if Stock.Materiels(i).Etat then
                Put (" En service. ");
            else
                Put(" Hors Service. ");
            end if;
            New_Line;
        end loop;
    end Afficher;

    procedure Supprimer_Material_Hors_Fonctionnement (Stock: in out T_Stock) is
        Nb_Materiels: Integer;
        i: Integer;
    begin
        i:=1;
        Nb_Materiels := Stock.Nb_Materiels;
        while i<= Nb_Materiels loop
            if not Stock.Materiels(i).Etat then 
                for j in i..(Nb_Materiels-1) loop
                    Stock.Materiels(j).Numero_Serie:=Stock.Materiels(j+1).Numero_Serie;
                    Stock.Materiels(j).Nature:=Stock.Materiels(j+1).Nature;
                    Stock.Materiels(j).Annee_Achat:=Stock.Materiels(j+1).Annee_Achat;
                    Stock.Materiels(j).Etat:=Stock.Materiels(j+1).Etat;
                end loop;
                Stock.Nb_Materiels:=Stock.Nb_Materiels-1;
                Nb_Materiels := Nb_Materiels -1;
            end if;
            i:=i+1;
        end loop;
    end Supprimer_Material_Hors_Fonctionnement;


end Stocks_Materiel;
