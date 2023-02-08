with Ada.Text_IO;       use Ada.Text_IO;
with Ada.Float_Text_IO; use Ada.Float_Text_IO;
with Vecteurs_Creux;    use Vecteurs_Creux;

-- Exemple d'utilisation des vecteurs creux.
procedure Exemple_Vecteurs_Creux is

	V0: T_Vecteur_Creux;
	Epsilon: constant Float := 1.0e-5;
begin
	Put_Line ("Début du scénario");
    -- TODO : à compléter
    Initialiser(V0);

    pragma Assert (Est_Nul (V0));

    Modifier(V0,1, 1.0);
    --Modifier (V0, 3, 4.0);
    --Modifier (V0, 4, 4.0);
    --Modifier (V0, 2, 2.0);
    --Modifier (V0, 3, 3.0);


    Detruire(V0);
    Put_Line ("Fin du scénario");
end Exemple_Vecteurs_Creux;
