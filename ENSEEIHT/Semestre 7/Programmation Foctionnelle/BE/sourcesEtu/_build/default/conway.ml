(* Exercice 1*)

(* max : int list -> int  *)
(* Paramètre : liste dont on cherche le maximum *)
(* Précondition : la liste n'est pas vide *)
(* Résultat :  l'élément le plus grand de la liste *)
let max l =
  List.fold_left (fun x y -> if x > y then x else y) (List.hd l) l  

(* TO DO : copier / coller les tests depuis conwayTests.txt *)
(************ tests de max ************)
let%test _ = max [ 1 ] = 1
let%test _ = max [ 1; 2 ] = 2
let%test _ = max [ 2; 1 ] = 2
let%test _ = max [ 1; 2; 3; 4; 3; 2; 1 ] = 4

(* max_max : int list list -> int  *)
(* Paramètre : la liste de listes dont on cherche le maximum *)
(* Précondition : il y a au moins un élement dans une des listes *)
(* Résultat :  l'élément le plus grand de la liste *)
let max_max ll =
  max (List.map (fun l -> max l) ll)

(* TO DO : copier / coller les tests depuis conwayTests.txt *)
(************ tests de max_max ************)
let%test _ = max_max [ [ 1 ] ] = 1
let%test _ = max_max [ [ 1 ]; [ 2 ] ] = 2
let%test _ = max_max [ [ 2 ]; [ 2 ]; [ 1; 1; 2; 1; 2 ] ] = 2
let%test _ = max_max [ [ 2 ]; [ 1 ] ] = 2
let%test _ = max_max [ [ 1; 1; 2; 1 ]; [ 1; 2; 2 ] ] = 2

let%test _ =
  max_max [ [ 1; 1; 1 ]; [ 2; 1; 2 ]; [ 3; 2; 1; 4; 2 ]; [ 1; 3; 2 ] ] = 4

(* Exercice 2*)

(* suivant : int list -> int list *)
(* Calcule le terme suivant dans une suite de Conway *)
(* Paramètre : le terme dont on cherche le suivant *)
(* Précondition : paramètre différent de la liste vide *)
(* Retour : le terme suivant *)

let suivant l = (*A améliorer*)
  let rec aux l acc e =
    match l with
    | [] -> [acc; e]
    | x::t -> if x = e then aux t (acc+1) e else acc::e::(aux l 0 x)
  in aux l 0 (List.hd l)

(* TO DO : copier / coller les tests depuis conwayTests.txt *)
(************ tests de suivant ************)
let%test _ = suivant [ 1 ] = [ 1; 1 ]
let%test _ = suivant [ 2 ] = [ 1; 2 ]
let%test _ = suivant [ 3 ] = [ 1; 3 ]
let%test _ = suivant [ 1; 1 ] = [ 2; 1 ]
let%test _ = suivant [ 1; 2 ] = [ 1; 1; 1; 2 ]
let%test _ = suivant [ 1; 1; 1; 1; 3; 3; 4 ] = [ 4; 1; 2; 3; 1; 4 ]
let%test _ = suivant [ 1; 1; 1; 3; 3; 4 ] = [ 3; 1; 2; 3; 1; 4 ]
let%test _ = suivant [ 1; 3; 3; 4 ] = [ 1; 1; 2; 3; 1; 4 ]
let%test _ = suivant [3;3] = [2;3]

(* suite : int -> int list -> int list list *)
(* Calcule la suite de Conway *)
(* Paramètre taille : le nombre de termes de la suite que l'on veut calculer *)
(* Paramètre depart : le terme de départ de la suite de Conway *)
(* Résultat : la suite de Conway *)
let suite n l = (*A améliorer*)
  let rec aux n l ll =
    if n=1 then ll
    else let suivant = suivant l in aux (n-1) suivant (ll @ [suivant])
  in aux n l [l]

(* TO DO : copier / coller les tests depuis conwayTests.txt *)
let%test _ = suite 1 [ 1 ] = [ [ 1 ] ]
let%test _ = suite 2 [ 1 ] = [ [ 1 ]; [ 1; 1 ] ]
let%test _ = suite 3 [ 1 ] = [ [ 1 ]; [ 1; 1 ]; [ 2; 1 ] ]
let%test _ = suite 4 [ 1 ] = [ [ 1 ]; [ 1; 1 ]; [ 2; 1 ]; [ 1; 2; 1; 1 ] ]

let%test _ =
  suite 5 [ 1 ]
  = [ [ 1 ]; [ 1; 1 ]; [ 2; 1 ]; [ 1; 2; 1; 1 ]; [ 1; 1; 1; 2; 2; 1 ] ]

let%test _ =
  suite 10 [ 1 ]
  = [
      [ 1 ];
      [ 1; 1 ];
      [ 2; 1 ];
      [ 1; 2; 1; 1 ];
      [ 1; 1; 1; 2; 2; 1 ];
      [ 3; 1; 2; 2; 1; 1 ];
      [ 1; 3; 1; 1; 2; 2; 2; 1 ];
      [ 1; 1; 1; 3; 2; 1; 3; 2; 1; 1 ];
      [ 3; 1; 1; 3; 1; 2; 1; 1; 1; 3; 1; 2; 2; 1 ];
      [ 1; 3; 2; 1; 1; 3; 1; 1; 1; 2; 3; 1; 1; 3; 1; 1; 2; 2; 1; 1 ];
    ]

let%test _ =
  suite 10 [ 3; 3 ]
  = [
      [ 3; 3 ];
      [ 2; 3 ];
      [ 1; 2; 1; 3 ];
      [ 1; 1; 1; 2; 1; 1; 1; 3 ];
      [ 3; 1; 1; 2; 3; 1; 1; 3 ];
      [ 1; 3; 2; 1; 1; 2; 1; 3; 2; 1; 1; 3 ];
      [ 1; 1; 1; 3; 1; 2; 2; 1; 1; 2; 1; 1; 1; 3; 1; 2; 2; 1; 1; 3 ];
      [ 3; 1; 1; 3; 1; 1; 2; 2; 2; 1; 1; 2; 3; 1; 1; 3; 1; 1; 2; 2; 2; 1; 1; 3 ];
      [ 1; 3; 2; 1; 1; 3; 2; 1; 3; 2; 2; 1; 1; 2; 1; 3; 2; 1; 1; 3; 2; 1; 3; 2; 2; 1; 1; 3; ];
      [ 1; 1; 1; 3; 1; 2; 2; 1; 1; 3; 1; 2; 1; 1; 1; 3; 2; 2; 2; 1; 1; 2; 1; 1; 1; 3; 1; 2; 2; 1; 1; 3; 1; 2; 1; 1; 1; 3; 2; 2; 2; 1; 1; 3; ];
    ]
(* Tests de la conjecture *)
(* "Aucun terme de la suite, démarant à 1, ne comporte un chiffre supérieur à 3" *)
(* TO DO *)
let%test _ = 
  let rec test_i i resultat_test =
    if i=0 then resultat_test
    else test_i (i-1) (resultat_test || (max_max (suite i [1]) <= 3))
  in test_i 10 true

let%test _ = max_max (suite 1 [1]) <= 3
let%test _ = max_max (suite 10 [1]) <= 3
let%test _ = max_max (suite 15 [1]) <= 3
let%test _ = max_max (suite 20 [1]) <= 3

(* Remarque : TO DO *)
(* Je pense que cette technique de vérification de la propriété  *)
(* "Aucun terme de la suite, démarant à 1, ne comporte un chiffre supérieur à 3"  *)
(* n'est pas fiable parce qu'on ne peut pas tester la totalité des élements de    *)
(* la suite. La complexité de la fonction suite nous limite quant aux nombres     *)
(* que l'on peut générer. Il faudrait utiliser une méthode plus généraliste.      *)