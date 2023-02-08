(* Exercice 3 *)
module type Expression = sig
  (* Type pour représenter les expressions *)
  type exp


  (* eval : exp -> int  *)
  (* Fonction permettant l'évaluation de la valeur d'une expression *)
  (* Paramètre e : exp expression à évaluer *)
  (* Précondition :  *)
  (* Résultat val : int entier représentant la valeur d'une expression *)
  (* Postcondition : *)

  val eval : exp -> int
end

(* Exercice 4 *)

(* TO DO avec l'aide du fichier  expressionArbreBinaire.txt *)

module ExpAvecArbreBinaire : Expression =
struct
(* Type pour représenter les expressions binaires *)
  type op = Moins | Plus | Mult | Div
  type exp = Binaire of exp * op * exp | Entier of int

  (* eval *)
  let rec eval arbre =
    match arbre with
    | Entier n -> n
    | Binaire (n1, op, n2) -> match op with
                              | Moins -> ((eval n1) - (eval n2))
                              | Plus -> ((eval n1) + (eval n2))
                              | Mult -> ((eval n1) * (eval n2))
                              | Div -> ((eval n1) / (eval n2))

  (* test eval *)
  let arbreBinaire0 = Entier 10
  let arbreBinaire1 = Binaire ((Binaire(Entier 3, Plus, Entier 4)), Moins, Entier 12)
  let arbreBinaire2 =  Binaire ((Binaire(Entier 2, Moins, Entier 1)), Plus, (Binaire(Entier 1, Moins, Entier 2)))
  let arbreBinaire4 = Binaire ((Binaire(Entier 3, Plus, Entier 4)), Plus, Entier 12)
  let arbreBinaire5 = Binaire (Entier 3, Plus,(Binaire(Entier 4, Plus, Entier 12)))
  let arbreBinaire6 = Binaire ((Binaire(Entier 3, Mult, Entier 4)), Plus, Entier 12)
  let arbreBinaire7 = Binaire ((Binaire(Entier 3, Mult, Entier 4)), Div, Entier 12)

  let%test _ = eval arbreBinaire0 = 10
  let%test _ = eval arbreBinaire1 = -5
  let%test _ = eval arbreBinaire2 = 0
  let%test _ = eval arbreBinaire4 = eval arbreBinaire5
  let%test _ = eval arbreBinaire6 = 24
  let%test _ = eval arbreBinaire7 = 1
end

(* Exercice 5 *)

(* TO DO avec l'aide du fichier  expressionArbreNaire.txt *)
module ExpAvecArbreNaire : Expression =
struct

  (* Linéarisation des opérateurs binaire associatif gauche et droit *)
  type op = Moins | Plus | Mult | Div
  type exp = Naire of op * exp list | Valeur of int
  
  (* bienformee : exp -> bool *)
  (* Vérifie qu'un arbre n-aire représente bien une expression n-aire *)
  (* c'est-à-dire que les opérateurs d'addition et multiplication ont au moins deux opérandes *)
  (* et que les opérateurs de division et soustraction ont exactement deux opérandes.*)
  (* Paramètre : l'arbre n-aire dont ont veut vérifier si il correspond à une expression *)
  let rec bienformee exp = 
    match exp with
    | Valeur _ -> true
    | Naire (op, l) -> match l, op with
                        | [], _ -> false
                        | [_], _ -> false
                        | _::_::_, (Plus | Mult) -> (List.fold_left (fun x y-> x && (bienformee y)) true l)
                        | x1::x2::t, (Moins | Div) -> if t = [] then (bienformee x1) && (bienformee x2) else false

  let en1 = Naire (Plus, [ Valeur 3; Valeur 4; Valeur 12 ])
  let en2 = Naire (Moins, [ en1; Valeur 5 ])
  let en3 = Naire (Mult, [ en1; en2; en1 ])
  let en4 = Naire (Div, [ en3; Valeur 2 ])
  let en1err = Naire (Plus, [ Valeur 3 ])
  let en2err = Naire (Moins, [ en1; Valeur 5; Valeur 4 ])
  let en3err = Naire (Mult, [ en1 ])
  let en4err = Naire (Div, [ en3; Valeur 2; Valeur 3 ])

  let%test _ = bienformee en1
  let%test _ = bienformee en2
  let%test _ = bienformee en3
  let%test _ = bienformee en4
  let%test _ = not (bienformee en1err)
  let%test _ = not (bienformee en2err)
  let%test _ = not (bienformee en3err)
  let%test _ = not (bienformee en4err)

  (* eval : exp-> int *)
  (* Calcule la valeur d'une expression n-aire *)
  (* Paramètre : l'expression dont on veut calculer la valeur *)
  (* Précondition : l'expression est bien formée *)
  (* Résultat : la valeur de l'expression *)
  let rec eval_bienformee exp =
    match exp with
    | Valeur x -> x
    | Naire(op, l) -> match op with
                    | Plus -> List.fold_right (fun x y -> x + y) (List.map (fun e -> eval_bienformee e) l) 0
                    | Moins -> List.fold_right (fun x y -> x - y) (List.map (fun e -> eval_bienformee e) l) 0
                    | Mult -> List.fold_right (fun x y -> x * y) (List.map (fun e -> eval_bienformee e) l) 1
                    | Div -> List.fold_right (fun x y -> x / y) (List.map (fun e -> eval_bienformee e) l) 1

  let%test _ = eval_bienformee en1 = 19
  let%test _ = eval_bienformee en2 = 14
  let%test _ = eval_bienformee en3 = 5054
  let%test _ = eval_bienformee en4 = 2527

  (* Définition de l'exception Malformee *)
  (* TO DO *)
    exception Malformee
  (* eval : exp-> int *)
  (* Calcule la valeur d'une expression n-aire *)
  (* Paramètre : l'expression dont on veut calculer la valeur *)
  (* Résultat : la valeur de l'expression *)
  (* Exception  Malformee si le paramètre est mal formé *)
  let eval exp = 
    if bienformee exp then eval_bienformee exp
    else raise Malformee

  let%test _ = eval en1 = 19
  let%test _ = eval en2 = 14
  let%test _ = eval en3 = 5054
  let%test _ = eval en4 = 2527

  let%test _ =
    try
      let _ = eval en1err in
      false
    with Malformee -> true

  let%test _ =
    try
      let _ = eval en2err in
      false
    with Malformee -> true

  let%test _ =
    try
      let _ = eval en3err in
      false
    with Malformee -> true

  let%test _ =
    try
      let _ = eval en4err in
      false
    with Malformee -> true

end