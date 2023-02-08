with Ada.Text_IO;
use  Ada.Text_IO;
with Dates;
use Dates;

procedure Exemple_Dates_Erreurs is
    Une_Date : T_Date;
    Mois_Suivant : T_Mois;
    Autre_Date : T_Date;
begin
    -- Initialiser une date
    Initialiser (Une_Date, 1, OCTOBRE, 2018);

    -- L'afficher
    Afficher (Une_Date);
    New_Line;

    -- Afficher un enter sur 2 positions
    --Afficher_Deux_Positions (2);-- Le compilateur ne reconnaît pas la fonction Afficher_Deux_Positions parce qu'elle n'est pas définie dans la spécification du module dates.ads
    New_Line;

    -- Afficher le mois suivant de Une_Date
    Mois_Suivant := T_Mois'succ (Le_Mois (Une_Date));
    Put ("Mois suivant : ");
    Put (T_Mois'Image (Mois_Suivant));
    New_Line;
    -- OK car le type T_Mois est accessible de l'utilisateur.

    -- Modifier directement la date
    --Une_Date.jour := 15;--Le type T_Date étant défini "private" dans dates.ads, on ne peut accéder à ces champs directement mais plutôt en utilisant les fonctions définis dans la spécification.
    --Une_Date.Mois := Mois_Suivant;--Même justification
    Afficher (Une_Date);
    New_Line;

    -- Illustrer les opérations possibles sur T_Date, type privé
    Autre_Date := Une_Date;
    Put ("Autre date : ");
    Afficher (Autre_Date);
    New_Line;

    if Autre_Date = Une_Date then
        Put_Line ("Ce sont les mêmes dates !");
    else
        Put_Line ("Les dates sont différentes !");
    end if;

end Exemple_Dates_Erreurs;
