package body TH is

    -- initialisation de chacune des listes contenues dans la table de hacahge
	procedure Initialiser(th: out T_TH) is
	begin
        for i in 1..capacite loop
            TH_LCA.Initialiser(th(i));
        end loop;
    end Initialiser;

    -- Revient à tester si toutes les listes contenues dans la tableau sont vides
	function Est_Vide (th : in T_TH) return Boolean is
	begin
        for i in 1..capacite loop
            if  not TH_LCA.Est_Vide(th(i)) then -- on retourne faux dès que l'une des listes n'es pas vide
                return false;
            end if;
        end loop;
        return true;
    end Est_Vide;

    -- somme des tailles de chacune des listes contenues dans la table de hacahge
    function Taille (th : in T_TH) return Integer is
        taille: Integer;
    begin
        taille := 0;
        for i in 1..capacite loop
            taille := taille + TH_LCA.Taille(th(i));
        end loop;
        return taille;
	end Taille;

    -- On utilse la fonction de hachage pour trouver la position de la liste où l'on doit insérer la nouvelle cle et sa donnée dans le tableau th
    -- On appelle par la suite la procédure enregistrer du module lca
    procedure Enregistrer (th : in  out  T_TH ; Cle : in T_Cle ; Donnee : in T_Donnee) is
	begin
        TH_LCA.Enregistrer(th(Hachage(Cle)),Cle, Donnee);
	end Enregistrer;

    -- On utilse la fonction de hachage pour trouver la position de la liste contenant la "Cle" dans le cas où elle serait présente dans le tableau th
    -- On appelle par la suite la fonction cle_presente du module lca
    function Cle_Presente (th : in  T_TH ; Cle : in T_Cle) return Boolean is
    begin
        return TH_LCA.Cle_presente(th(Hachage(Cle)),Cle);
    end Cle_Presente;

    -- On utilse la fonction de hachage pour trouver la position de la liste contenant la "Cle" dans le cas où elle serait présente dans le tableau th
    -- On appelle par la suite la fonction La_donnee du module lca
	function La_Donnee (th : in  T_TH ; Cle : in T_Cle) return T_Donnee is
    begin
        return TH_LCA.La_Donnee(th(Hachage(Cle)),Cle);
    end La_Donnee;

    -- On utilse la fonction de hachage pour trouver la position de la liste contenant la "Cle" dans le cas où elle serait présente dans le tableau th
    -- On appelle par la suite la procédure supprimer du module lca
	procedure Supprimer (th : in  out  T_TH ; Cle : in T_Cle) is
    begin
         TH_LCA.Supprimer(th(Hachage(cle)), Cle);
	end Supprimer;

    -- On vide chacune des listes présentes dans le table de hachage (qui est un tableau de liste)
    -- On utilise donc la procédure Vider du module LCA
	procedure Vider (th : in  out T_TH ) is
	begin
        for i in 1..capacite loop
            TH_LCA.Vider(th(i));
        end loop;
	end Vider;


    procedure Pour_Chaque (th : in  T_TH ) is
        procedure Traiter is new TH_LCA.Pour_Chaque(traiter);
    begin
        for i in 1..Capacite loop
            Traiter(th(i));
        end loop;

    end Pour_Chaque;


end TH;
