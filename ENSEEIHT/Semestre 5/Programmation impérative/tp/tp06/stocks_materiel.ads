
-- Auteur: 
-- Gérer un stock de matériel informatique.

package Stocks_Materiel is


    CAPACITE : constant Integer := 10;      -- nombre maximum de matériels dans un stock

    type T_Nature is (UNITE_CENTRALE, DISQUE, ECRAN, CLAVIER, IMPRIMANTE);
        
    type T_Materiel is 
        record
            Numero_Serie : Integer;
            Nature       : T_Nature;
            Annee_Achat  : Integer;
            Etat : Boolean; -- true s’il est en état de fonctionnement, false sinon
            -- Invariant
            --    Annee_Achat > 0
            --    Numero_Serie > 0
        end record;

    type T_Materiels is array (1..CAPACITE) of T_Materiel;
    
    type T_Stock is limited private;


    -- Créer un stock vide.
    --
    -- paramètres
    --     Stock : le stock à créer
    --
    -- Assure
    --     Nb_Materiels (Stock) = 0
    --
    procedure Creer (Stock : out T_Stock) with
        Post => Nb_Materiels (Stock) = 0;


    -- Obtenir le nombre de matériels dans le stock Stock.
    --
    -- Paramètres
    --    Stock : le stock dont ont veut obtenir la taille
    --
    -- Nécessite
    --     Vrai
    --
    -- Assure
    --     Résultat >= 0 Et Résultat <= CAPACITE
    --
    function Nb_Materiels (Stock: in T_Stock) return Integer with
        Post => Nb_Materiels'Result >= 0 and Nb_Materiels'Result <= CAPACITE;


    -- Enregistrer un nouveau métériel dans le stock.  Il est en
    -- fonctionnement.  Le stock ne doit pas être plein.
    -- 
    -- Paramètres
    --    Stock : le stock à compléter
    --    Numero_Serie : le numéro de série du nouveau matériel
    --    Nature       : la nature du nouveau matériel
    --    Annee_Achat  : l'année d'achat du nouveau matériel
    -- 
    -- Nécessite
    --    Nb_Materiels (Stock) < CAPACITE
    -- 
    -- Assure
    --    Nouveau matériel ajouté
    --    Nb_Materiels (Stock) = Nb_Materiels (Stock)'Avant + 1
    procedure Enregistrer (
            Stock        : in out T_Stock;
            Numero_Serie : in     Integer;
            Nature       : in     T_Nature;
            Annee_Achat  : in     Integer
        ) with
            Pre => Nb_Materiels (Stock) < CAPACITE,
            Post => Nb_Materiels (Stock) = Nb_Materiels (Stock)'Old + 1;
    
    -- Obtenir le nombre de matériels qui sont hors d’état de fonctionnement.
    --
    -- Paramètres
    --    Stock : le stock dont ont veut obtenir le nombre de matériels qui sont hors d’état de fonctionnement.
    --
    -- Nécessite
    --     Vrai
    --
    -- Assure
    --     Résultat >= 0 Et Résultat <= CAPACITE
    --
    function Nb_Materiels_Hors_Fonctionnement (Stock: in T_Stock) return Integer with
         Post => Nb_Materiels_Hors_Fonctionnement'Result >= 0 and Nb_Materiels_Hors_Fonctionnement'Result <= CAPACITE;

    -- Mettre à jour l’état d’un matériel enregistrer dans le stock à partir de son numéro de série.
    --
    -- Paramètres
    --    Stock : le stock contenant le matériel qu'on veut mettre à jour.
    --    Etat: le nouvel état.
    --    Numero_Serie: 
    --
    -- Nécessite
    --     Vrai
    --
    procedure Mettre_A_Jour (Stock: in out T_Stock; Etat : in Boolean ; Numero_Serie : in Integer);
    
    -- Supprimer du stock un matériel à partir de son numéro de série.
    --
    -- Paramètres
    --    Stock : le stock contenant le matériel qu'on veut mettre à jour.
    --    Numero_Serie: 
    --
    procedure Supprimer_Material (Stock: in out T_Stock; Numero_Serie : in Integer) ;
    
    --  Afficher tous les matériels du stock.
    --
    -- Paramètres
    --    Stock : le stock contenant le matériel qu'on veut mettre à jour. 
    --
    procedure Afficher (Stock: in T_Stock) ;
    
    --Supprimer tous les matériels qui ne sont pas en état de fonctionnement.
    --
    -- Paramètres
    --    Stock : le stock contenant le matériel qu'on veut mettre à jour.
    --
    procedure Supprimer_Material_Hors_Fonctionnement (Stock: in out T_Stock) ;
    
private 
    
    type T_Stock is 
        record
            Materiels: T_Materiels;
            Nb_Materiels: Integer;
        end record;

end Stocks_Materiel;
