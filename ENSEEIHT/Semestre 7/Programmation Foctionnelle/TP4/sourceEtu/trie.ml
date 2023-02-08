open Assoc
open Arbre
open Chaines

(* le type trie :
    triplet arbre,
            fonction de décomposition mot -> liste de caractères,
            fonction de recomposition liste de caractères -> mot *)
type ('a,'b) trie = Trie of ('b arbre) * ('a -> 'b list) * ('b list -> 'a)

(******************************************************************************)
(*   fonction de création d'un nouveau trie                                   *)
(*   signature  : nouveau :                                                   *)
(*          ('a -> 'b list) -> ('b list -> 'a) -> ('a, 'b) trie = <fun>       *)
(*   paramètres : - une fonction de décomposition                             *)
(*                     mot -> liste de caractères                             *)
(*                -  une fonction de recomposition                            *)
(*                     liste de caractères -> mot                             *)
(*   résultat     : un nouveau trie "vide"                                    *)
(******************************************************************************)
let nouveau fd fr = Trie(Noeud(false,[]), fd, fr)

(******************************************************************************)
(*   fonction d'appartenance d'un élément à un trie                           *)
(*   signature  : appartient : 'a -> ('a, 'b) trie -> bool = <fun>            *)
(*   paramètres : - un mot                                                    *)
(*                - un trie                                                   *)
(*   résultat   : le résultat booléen du test                                 *)
(******************************************************************************)
let appartient mot trie =
  match trie with
  | Trie (arbre, decomp, _) -> appartient_arbre (decomp mot) arbre

let appartient_v2 mot trie =
  match trie with
  | Trie (arbre, decomp, _) -> let l= decomp mot in appartient_arbre l arbre

(******************************************************************************)
(*   fonction d'ajout d'un élément dans un trie                               *)
(*   signature  : ajout : 'a -> ('a, 'b) trie -> ('a, 'b) trie = <fun>        *)
(*   paramètres : - un mot                                                    *)
(*                - un trie                                                   *)
(*   résultat   : le trie avec le mot ajouté                                  *)
(******************************************************************************)
let ajout mot (Trie(arbre, decompose, recompose)) =
  Trie (ajout_arbre (decompose mot) arbre,decompose,recompose)

(*  Pour les tests *)
let trie_sujet =
  List.fold_right ajout
    ["bas"; "bât"; "de"; "la"; "lai"; "laid"; "lait"; "lard"; "le"; "les"; "long"]
    (nouveau decompose_chaine recompose_chaine)

(******************************************************************************)
(*   fonction de retrait d'un élément d'un trie                               *)
(*   signature  : trie_retrait : 'a -> ('a, 'b) trie -> ('a, 'b) trie = <fun> *)
(*   paramètres : - un mot                                                    *)
(*                - un trie                                                   *)
(*   résultat   : le trie avec le mot retiré                                  *)
(******************************************************************************)
let retrait mot trie = 
    match trie with
    | Trie(arb,fd,fr) -> Trie(retrait_arbre (fd mot) arb,fd,fr) 

(******************************************************************************)
(*   fonction interne au Module qui génère la liste de tous les mots          *)
(*   d'un trie                                                                *)
(*   signature    : trie_dico : ('a, 'b) trie -> 'a list = <fun>              *)
(*   paramètre(s) : le trie                                                   *)
(*   résultat     : la liste des mots                                         *)
(******************************************************************************)
let trie_dico trie = 
  match trie with
| Trie (arbre, _, recomp) -> List.map recomp (liste_elements arbre)

(******************************************************************************)
(* procédure d'affichage d'un trie                                            *)
(*   signature  : affiche : ('a -> unit) -> ('a, 'b) trie -> unit = <fun>     *)
(*   paramètres : - une procédure d'affichage d'un mot                        *)
(*                - un trie                                                   *)
(*   résultat   : aucun                                                       *)
(******************************************************************************)
let affiche p trie = 
  let liste_mots = trie_dico trie in
  List.map p liste_mots

(******************************************************************************)
(*   fonction de retrait d'un élément d'un trie avec normalisation                               *)
(*   signature  : trie_retrait : 'a -> ('a, 'b) trie -> ('a, 'b) trie = <fun> *)
(*   paramètres : - un mot                                                    *)
(*                - un trie                                                   *)
(*   résultat   : le trie avec le mot retiré                                  *)
(******************************************************************************)
let retrait mot trie = match trie with
    | Trie(arb,fd,fr) -> Trie(retrait_arbre (fd mot) arb,fd,fr) and (normalisation arb)

(* Tests Unitaires *)

(* appartient *)
let%test _ = appartient "bas"  trie_sujet
let%test _ = appartient "bât"  trie_sujet
let%test _ = appartient "de"  trie_sujet
let%test _ = appartient "la"  trie_sujet
let%test _ = appartient "lai"  trie_sujet
let%test _ = appartient "laid"  trie_sujet
let%test _ = appartient "lait"  trie_sujet
let%test _ = appartient "lard"  trie_sujet
let%test _ = appartient "le"  trie_sujet
let%test _ = appartient "les"  trie_sujet
let%test _ = appartient "long"  trie_sujet
let%test _ = not (appartient "lardi"  trie_sujet)
let%test _ = not (appartient "lol"  trie_sujet)
let%test _ = not (appartient "base"  trie_sujet)
let%test _ = not (appartient "laide"  trie_sujet)
let%test _ = not (appartient "las"  trie_sujet)

(* retrait *)
let%test _ = 
let remove_1_trie_sujet = retrait "bas" trie_sujet in
   not ( appartient "bas" remove_1_trie_sujet)
   && appartient "bat" remove_1_trie_sujet
   && appartient "de" remove_1_trie_sujet
   && appartient "la" remove_1_trie_sujet
   && appartient "lai" remove_1_trie_sujet
   (*&& appartient "laid" remove_1_trie_sujet
   && appartient "long" remove_1_trie_sujet
   && appartient "lait" remove_1_trie_sujet
   && appartient "lard" remove_1_trie_sujet
   && appartient "le" remove_1_trie_sujet
   && appartient "les" remove_1_trie_sujet
   && appartient "long" remove_1_trie_sujet*)

(* trie_dico *)
let%test _ = appartient "bas"  trie_sujet
let%test _ = appartient "bât"  trie_sujet
let%test _ = appartient "de"  trie_sujet
let%test _ = appartient "la"  trie_sujet
let%test _ = appartient "lai"  trie_sujet

(* affiche *)
let%test _ = appartient "bas"  trie_sujet
let%test _ = appartient "bât"  trie_sujet
let%test _ = appartient "de"  trie_sujet
let%test _ = appartient "la"  trie_sujet
let%test _ = appartient "lai"  trie_sujet