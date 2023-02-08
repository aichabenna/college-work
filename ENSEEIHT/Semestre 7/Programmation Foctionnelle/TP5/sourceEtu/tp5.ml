(* Evaluation des expressions simples *)

(* Module abstrayant les expressions *)
module type ExprSimple =
sig
  type t
  val const : int -> t
  val plus : t -> t -> t
  val mult : t-> t -> t
end

(* Module réalisant l'évaluation d'une expression *)
module EvalSimple : ExprSimple with type t = int =
struct
  type t = int
  let const c = c
  let plus e1 e2 = e1 + e2
  let mult e1 e2 = e1 * e2
end


(* Solution 1 pour tester *)
(* A l'aide de foncteur *)

(* Définition des expressions *)
module ExemplesSimples (E:ExprSimple) =
struct
  (* 1+(2*3) *)
  let exemple1  = E.(plus (const 1) (mult (const 2) (const 3)) )
  (* (5+2)*(2*3) *)
  let exemple2 =  E.(mult (plus (const 5) (const 2)) (mult (const 2) (const 3)) )
end

(* Module d'évaluation des exemples *)
module EvalExemples =  ExemplesSimples (EvalSimple)

let%test _ = (EvalExemples.exemple1 = 7)
let%test _ = (EvalExemples.exemple2 = 42)

(* Module réalisant la conversion d'une expression en chaine de caractère *)
module PrintSimple : ExprSimple with type t = string =
struct
  type t = string
  let const c = string_of_int(c)
  let plus e1 e2 = "(" ^ e1 ^ "+" ^ e2 ^ ")"
  let mult e1 e2 = "(" ^ e1 ^ "*" ^ e2 ^ ")"
end

(* Module d'évaluation des exemples *)
module EvalExemplesPrint =  ExemplesSimples (PrintSimple)

let%test _ = (EvalExemplesPrint.exemple1 = "(1+(2*3))")
let%test _ = (EvalExemplesPrint.exemple2 = "((5+2)*(2*3))")

(* Module réalisant le compte des operations dans une expression *)
module CompteSimple : ExprSimple with type t = int =
struct
  type t = int
  let const c = 0
  let plus e1 e2 = 1 + e1 + e2 (* e1 et e2 peuvent être de la forme plus x y ou mult x y*)
  let mult e1 e2 = 1 + e1 + e2
end

(* Module d'évaluation des exemples *)
module EvalExemplesCompte =  ExemplesSimples (CompteSimple)

let%test _ = (EvalExemplesCompte.exemple1 = 2)
let%test _ = (EvalExemplesCompte.exemple2 = 3)

(* Interface permettant d’abstraire la présence de variable dans les expressions*)
module type ExprVar =
sig
  type t
  val def : string -> t -> t -> t
  val var : string -> t 
end

(* inclusion d'interfaces *)

(* Interface permettant d’abstraire les expressions dans leur intégralité*)
module type Expr =
sig
  include ExprSimple
  include (ExprVar with type t := t)
end

(* Module réalisant la conversion d'une expression en chaine de caractère *)
module PrintVar : ExprVar with type t = string =
struct
  type t = string
  let def s e1 e2 = "let " ^ s ^ "=" ^ e1 ^ " in " ^ e2
  let var s = s
end

(* Définition des expressions *)
module ExemplesVar (E:ExprVar) =
struct
  (* let x=a in b  *)
  let exemple1  = E.(def "x" (var "a") (var "b"))
  (* let x=w in let y=x in z *)
  let exemple2 =  E.(def "x" (var "w") (def "y" (var "x") (var "z")))
end

(* Module d'évaluation des exemples *)
module EvalExemplesPrintVar =  ExemplesVar (PrintVar)

let%test _ = (EvalExemplesPrintVar.exemple1 = "let x=a in b")
let%test _ = (EvalExemplesPrintVar.exemple2 = "let x=w in let y=x in z")

(* Module réalisant le traitement d'une expression dans son intégralité *)
module Print : Expr with type t = string =
struct
  include PrintSimple
  include (PrintVar : ExprVar with type t := t)
end

(* Définition des expressions *)
module Exemples (E:Expr) =
struct
  (* 1+(2*3) *)
  let exemple1  = E.(plus (const 1) (mult (const 2) (const 3)) )
  (* (5+2)*(2*3) *)
  let exemple2 =  E.(mult (plus (const 5) (const 2)) (mult (const 2) (const 3)) )

  (* let x=a in b  *)
  let exemple3  = E.(def "x" (var "a") (var "b"))
  (* let x=w in let y=x in z *)
  let exemple4 =  E.(def "x" (var "w") (def "y" (var "x") (var "z")))

  (* let x=2 in (x+3)  *)
  let exemple5  = E.(def "x" (const 2) (plus (var "x") (const 3)) )
  (* let x=(a+2) in ((x+2)*(y*3)) *)
  let exemple6 =  E.(def "x" (plus (var "a") (const 2)) (mult (plus (var "x") (const 2)) (mult (var "y") (const 3))) )
end

(* Module d'évaluation des exemples *)
module EvalExemplesAll =  Exemples (Print)

let%test _ = (EvalExemplesAll.exemple1 = "(1+(2*3))")
let%test _ = (EvalExemplesAll.exemple2 = "((5+2)*(2*3))")
let%test _ = (EvalExemplesAll.exemple3 = "let x=a in b")
let%test _ = (EvalExemplesAll.exemple4 = "let x=w in let y=x in z")
let%test _ = (EvalExemplesAll.exemple5 = "let x=2 in (x+3)")
let%test _ = (EvalExemplesAll.exemple6 = "let x=(a+2) in ((x+2)*(y*3))")

type env = (string∗int) list

module EvalVar : ExprVar with type t = string =
struct
  type t = env -> int
  let def x e1 e2 = fun e -> e2 ((x, e1 e)::e)
  let var x = fun e -> List.assoc x e
end

(*module EvalSimpleEnv : ExprSimple with type t = int =
struct
  type t = int
  let const c = c
  let plus e1 e2 = e1 + e2
  let mult e1 e2 = e1 * e2
end*)

(*module Eval : Expr with type t = string =
struct
  include PrintSimple
  include (PrintVar : ExprVar with type t := t)
end*)