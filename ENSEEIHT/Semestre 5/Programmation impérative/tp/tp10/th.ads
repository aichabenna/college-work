with LCA;

generic

    type T_Cle is private;
    type T_Donnee is private;
    Capacite : Integer;
    with function Hachage (CLe: in T_cle) return Integer;


package TH is

    -- Instanciation du type T_LCA
    package TH_LCA is
            new LCA (T_Cle => T_cle, T_Donnee => T_Donnee);
    use TH_LCA;

	type T_TH is limited private;

	-- Initialiser une Sda.  La Sda est vide.
	procedure Initialiser(th: out T_TH) with
		Post => Est_Vide (th);

	-- Est-ce qu'une th est vide ?
	function Est_Vide (th : in T_TH) return Boolean;


	-- Obtenir le nombre d'éléments d'une Sda.
	function Taille (th : in   T_TH ) return Integer with
		Post => Taille'Result >= 0
			and (Taille'Result = 0) = Est_Vide (th);


	-- Enregistrer une Donnée associée à une Clé dans une th.
	-- Si la clé est déjà présente dans la Sda, sa donnée est changée.
	procedure Enregistrer (th : in  out  T_TH ; Cle : in T_Cle ; Donnee : in T_Donnee ) with
		Post => Cle_Presente (th, Cle) and (La_Donnee (th, Cle) = Donnee)   -- donnée insérée
				and (not (Cle_Presente (th, Cle)'Old) or Taille (th) = Taille (th)'Old)
				and (Cle_Presente (th, Cle)'Old or Taille (th) = Taille (th)'Old + 1);

	-- Supprimer la Donnée associée à une Clé dans une Sda.
	-- Exception : Cle_Absente_Exception si Clé n'est pas utilisée dans la Sda
	procedure Supprimer (th : in  out  T_TH ; Cle : in T_Cle) with
		Post =>  Taille (th) = Taille (th)'Old - 1 -- un élément de moins
			and not Cle_Presente (th, Cle);         -- la clé a été supprimée


	-- Savoir si une Clé est présente dans une Sda.
	function Cle_Presente (th : in  T_TH ; Cle : in T_Cle) return Boolean;


	-- Obtenir la donnée associée à une Cle dans la Sda.
	-- Exception : Cle_Absente_Exception si Clé n'est pas utilisée dans l'Sda
	function La_Donnee (th : in  T_TH ; Cle : in T_Cle) return T_Donnee;


	-- Supprimer tous les éléments d'une Sda.
	procedure Vider (th : in out T_TH ) with
		Post => Est_Vide (th);


	-- Appliquer un traitement (Traiter) pour chaque couple d'une Sda.
	generic
		with procedure Traiter (Cle : in T_Cle; Donnee: in T_Donnee);
	procedure Pour_Chaque (th : in  T_TH );


-- AVEC_AFFICHER_DEBUG START DELETE
	-- Afficher la Sda en révélant sa structure interne.
	--generic
	--	with procedure Afficher_Cle (Cle : in T_Cle);
	--	with procedure Afficher_Donnee (Donnee : in T_Donnee);
	-- procedure Afficher_Debug (Sda : in T_LCA);

-- AVEC_AFFICHER_DEBUG STOP DELETE
private
    -- T_TH: Tableau de listes T_LCA
    type T_TH  is array (1..Capacite) of T_LCA;

end TH;
