with Ada.Text_IO;           use Ada.Text_IO;
with Ada.Integer_Text_IO;   use Ada.Integer_Text_IO;
with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;

with LCA;

procedure LCA_Sujet is

    -- Instanciation du type T_LCA tel que:
    -- La clé est une chaine de caractères et la donnée est un entier
    	package LCA_String_Integer is
		new LCA (T_Cle => Unbounded_String, T_Donnee => Integer);
    use LCA_String_Integer;

    -- Implémentation de Afficher
    procedure Afficher (S : in Unbounded_String; N: in Integer) is
	begin
		Put (To_String (S));
		Put (" : ");
		Put (N, 1);
		New_Line;
    end Afficher;

    -- Instanciation du la procédure Pour_Chaque tq traiter = afficher
	procedure Afficher is
		new Pour_Chaque (Afficher);

    L: T_LCA;

begin
    -- Initialisation de la liste
    Initialiser(L);

    -- Enregistrement des deux cellules
    Enregistrer(L, To_Unbounded_String("un"),1);
    Enregistrer(L,To_Unbounded_String("deux"), 2);

    -- Affichage des éléments de la listes
    Afficher(L);

    -- Désallocation de la mémoire
    Vider(L);
end LCA_Sujet;
