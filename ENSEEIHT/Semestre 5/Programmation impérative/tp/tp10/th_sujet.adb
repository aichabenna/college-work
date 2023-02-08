--Écrire un programme (fichier th_sujet.adb) qui crée une table de hachage de taille 11, dont
--les clés sont des chaînes, les données des entiers et la fonction de hachage la longueur de la
--clé. Ce programme enregistrera ensuite dans cette table les valeurs entières 1, 2, 3, 4, 5, 99 et
--21 avec les clés respectives "un", "deux", "trois", "quatre", "cinq", "quatre-vingt-dix-neuf" et
--"vingt-et-un". Enfin, il affichera le contenu de la table
with Ada.Text_IO;           use Ada.Text_IO;
with Ada.Integer_Text_IO;   use Ada.Integer_Text_IO;
with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;

with TH;

procedure TH_Sujet is

    -- Implémentation de la fonction de hachage qui, ici calcule la longueur de la clé (chaine de caractères)
    function Hachage(Cle: in Unbounded_String) return Integer is
        Longueur_Cle : Integer;
    begin
        Longueur_Cle := Length(Cle);
        if  Longueur_Cle <11 then
            return Longueur_Cle;
        end if;
        return (Longueur_Cle mod 11) +1;
        -- Dans le cas où Longueur_Cle >= 11 on lui applique le modulo pour rester dans l'intervalle des des indices possibles ici ( 1 à 11)
        -- On ajoute +1 pour éviter le cas de 0 quand Longueur_Cle = 11 * K
    end Hachage;

    -- Instanciation de la table de hachage tq:
    -- La clé est une chaine de caractères
    -- La donnée est un entier
    -- La capacité est à 11
    -- La fonction de hacahage calcule la longueur de la clé
    	package TH_String_Integer is
		new TH (T_Cle => Unbounded_String, T_Donnee => Integer, Capacite => 11 , Hachage => Hachage );
    use TH_String_Integer;

    -- Implémentation de la fonction Afficher
    procedure Afficher (S : in Unbounded_String; N: in Integer) is
	begin
		Put (To_String (S));
		Put (" : ");
		Put (N, 1);
		New_Line;
	end Afficher;

    -- Instantciation de la fonction pour_chaque avec traiter = afficher
	procedure Afficher is
		new Pour_Chaque (Afficher);

    TH: T_TH;

begin
    -- Initialisation de la table de hachage
    Initialiser(TH);

    -- Enregistrement des éléments dans la table
    Enregistrer (th , To_Unbounded_String("un"),1 );
    Enregistrer (th , To_Unbounded_String("deux"),2 );
    Enregistrer (th , To_Unbounded_String("trois"),3 );
    Enregistrer (th , To_Unbounded_String("quatre"),4 );
    Enregistrer (th , To_Unbounded_String("cinq"),5 );
    Enregistrer (th , To_Unbounded_String("quatre-vingt-dix-neuf"),99 );
    Enregistrer (th , To_Unbounded_String("vingt-et-un"),21 );

    -- Affichage de la table
    Afficher(th);

    -- Désallocation de la mémoire
    Vider(th);
end TH_Sujet;
