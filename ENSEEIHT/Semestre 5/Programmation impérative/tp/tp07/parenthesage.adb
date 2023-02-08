with Piles;

procedure Parenthesage is


    -- L'indice dans la chaîne Meule de l'élément Aiguille.
    -- Si l'Aiguille n'est pas dans la Meule, on retroune Meule'Last + 1.
    Function Index (Meule : in String; Aiguille: Character) return Integer with
        Post => Meule'First <= Index'Result and then Index'Result <= Meule'Last + 1
            and then (Index'Result > Meule'Last or else Meule (Index'Result) = Aiguille)
    is
    begin
        for i in (Meule'First)..(Meule'Last) loop
            if Meule(i) = Aiguille then
                return i;
            end if;
        end loop;
        return Meule'Last + 1;   -- TODO : à corriger !
    end Index;


    -- Programme de test de Index.
    procedure Tester_Index is
        ABCDEF : constant String := "abcdef";
    begin
        pragma Assert (1 = Index (ABCDEF, 'a'));
        pragma Assert (3 = Index (ABCDEF, 'c'));
        pragma Assert (6 = Index (ABCDEF, 'f'));
        pragma Assert (7 = Index (ABCDEF, 'z'));
        pragma Assert (4 = Index (ABCDEF (1..3), 'z'));
        pragma Assert (3 = Index (ABCDEF (3..5), 'c'));
        pragma Assert (5 = Index (ABCDEF (3..5), 'e'));
        pragma Assert (6 = Index (ABCDEF (3..5), 'a'));
        pragma Assert (6 = Index (ABCDEF (3..5), 'g'));
    end;


    -- Vérifier les bon parenthésage d'une Chaîne (D).  Le sous-programme
    -- indique si le parenthésage est bon ou non (Correct : R) et dans le cas
    -- où il n'est pas correct, l'indice (Indice_Erreur : R) du symbole qui
    -- n'est pas appairé (symbole ouvrant ou fermant).
    --
    -- Exemples
    --   "[({})]"  -> Correct
    --   "]"       -> Non Correct et Indice_Erreur = 1
    --   "((()"    -> Non Correct et Indice_Erreur = 2
    --
    procedure Verifier_Parenthesage (Chaine: in String ; Correct : out Boolean ; Indice_Erreur : out Integer) is
        Ouvrants : Constant String := "([{";
        Fermants : Constant String := ")]}";
        package Pile_Caractere is
            new Piles(100, Character);
        use Pile_Caractere;
        Pile_Ouvrants: Pile_Caractere.T_Pile;
        package Pile_Integer is
            new Piles(100, Integer);
        use Pile_Integer;
        Pile_Indices: Pile_Integer.T_Pile;
        i: Integer;
    begin
        Initialiser(Pile_Ouvrants);
        Initialiser(Pile_Indices);
        for ouvrant in (Ouvrants'First)..(Ouvrants'Last) loop
                if Chaine(Chaine'First) = Ouvrants(ouvrant) then
                    Empiler (Pile_Ouvrants , Chaine(Chaine'First));
                    Empiler (Pile_Indices , Ouvrants'First);
                end if;
        end loop;
        i:= Chaine'First+1;
        Indice_Erreur := Chaine'First;
        correct:= not Est_Vide(Pile_Ouvrants);
        while i<= (Chaine'Last) and correct loop
            for j in 1..(Ouvrants'Last) loop
                if Chaine(i) = Ouvrants(j) then
                    Indice_Erreur := i;
                    Empiler (Pile_Ouvrants , Chaine(i));
                    Empiler (Pile_Indices , i);
                end if;
            end loop;

            for k in 1..(Fermants'Last) loop
                if Chaine(i) = Fermants(k) then
                    if not Est_Vide(Pile_Ouvrants) then
                        case Fermants(k) is
                        when '}'  =>
                            if (Sommet(Pile_Ouvrants) = '{') then
                                Indice_Erreur := Sommet(Pile_Indices);
                                Depiler (Pile_Indices);
                                Depiler (Pile_Ouvrants);
                            elsif (Sommet(Pile_Ouvrants) = '(') or (Sommet(Pile_Ouvrants) = '[') then
                                Indice_Erreur := i;
                                correct := false;
                            end if;
                        when ')' =>
                            if (Sommet(Pile_Ouvrants) = '(') then
                                Indice_Erreur := Sommet(Pile_Indices);
                                Depiler (Pile_Indices);
                                Depiler (Pile_Ouvrants);
                            elsif (Sommet(Pile_Ouvrants) = '{') or (Sommet(Pile_Ouvrants) = '[') then
                                Indice_Erreur := i;
                                correct := false;
                            end if;
                        when ']'  =>
                            if (Sommet(Pile_Ouvrants) = '[') then
                                Indice_Erreur := Sommet(Pile_Indices);
                                Depiler (Pile_Indices);
                                Depiler (Pile_Ouvrants);
                            elsif (Sommet(Pile_Ouvrants) = '{') or (Sommet(Pile_Ouvrants) = '(') then
                                Indice_Erreur := i;
                                correct := false;
                            end if;
                        when others => null;
                        end case;
                    else
                        Indice_Erreur := i;
                        correct := false;
                    end if;
                end if;
            end loop;
            i:=i+1;
        end loop;
    end Verifier_Parenthesage;



    -- Programme de test de Verifier_Parenthesage
    procedure Tester_Verifier_Parenthesage is
        Exemple1 : constant String(1..2) :=  "{}";
        Exemple2 : constant String(11..18) :=  "]{[(X)]}";

        Indice : Integer;   -- Résultat de ... XXX
        Correct : Boolean;
    begin
        Verifier_Parenthesage ("(a < b)", Correct, Indice);
        pragma Assert (Correct);

        Verifier_Parenthesage ("([{a}])", Correct, Indice);
        pragma Assert (Correct);

        Verifier_Parenthesage ("(][{a}])", Correct, Indice);
        pragma Assert (not Correct);
        pragma Assert (Indice = 2);

        Verifier_Parenthesage ("]([{a}])", Correct, Indice);
        pragma Assert (not Correct);
        pragma Assert (Indice = 1);

        Verifier_Parenthesage ("([{}])}", Correct, Indice);
        pragma Assert (not Correct);
        pragma Assert (Indice = 7);

        Verifier_Parenthesage ("([{", Correct, Indice);
        pragma Assert (not Correct);
        pragma Assert (Indice = 3);

        Verifier_Parenthesage ("([{}]", Correct, Indice);
        pragma Assert (not Correct);
        pragma Assert (Indice = 1);

        Verifier_Parenthesage ("", Correct, Indice);
        pragma Assert (Correct);

        Verifier_Parenthesage (Exemple1, Correct, Indice);
        pragma Assert (Correct);

        Verifier_Parenthesage (Exemple2, Correct, Indice);
        pragma Assert (not Correct);
        pragma Assert (Indice = 11);

        Verifier_Parenthesage (Exemple2(12..18), Correct, Indice);
        pragma Assert (Correct);

        Verifier_Parenthesage (Exemple2(12..15), Correct, Indice);
        pragma Assert (not Correct);
        pragma Assert (Indice = 14);
    end Tester_Verifier_Parenthesage;

begin
    Tester_Index;
    Tester_Verifier_Parenthesage;
end Parenthesage;
