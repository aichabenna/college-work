open Miniml_types

(* signature minimale pour définir des variables *)
module type VariableSpec =
  sig
    (* type abstrait des variables      *)
    type t

    (* création d'une variable fraîche  *)
    val fraiche : unit -> t

    (* fonctions de comparaison         *)
    (* permet de définir des conteneurs *)
    (* (hash-table, etc) de variables   *)
    val compare : t -> t -> int
    val equal : t -> t -> bool
    val hash : t -> int

    (* fonction d'affichage             *)
    (* on utilise Format.std_formatter  *)
    (* comme premier paramètre          *)
    (* pour la sortie standard          *) 
    val fprintf : Format.formatter -> t -> unit
  end

(* implantation de la spécification     *)
module TypeVariable : VariableSpec =
  struct
    type t = int

    let fraiche =
      let cpt = ref 0 in
      (fun () -> incr cpt; !cpt)

    let compare a b = a - b
    let equal a b = a = b
    let hash a = Hashtbl.hash a

    let fprintf fmt a = Format.fprintf fmt "t{%d}" a
  end

(* Module d'inference des types *)
module RegleTypage = 
struct

(* definition du type des equations *)
type 'a equ = ('a typ * 'a typ) (* exemple : tau = bool, alpha = tau... *)

(* definition du type de l'environnement *)
type 'a env = (ident * 'a typ) list

(*cherche un identifiant dans l'environnement
   id : identifiant a trouver
   en : environnement dans lequel chercher
   retourne : None si id n'est pas dans l'environnement, Some(t) sinon,
   avec le t le type associe a id dans l'environnement*)
let rec cherche : ident -> 'a env -> 'a typ option = fun id en -> 
  match en with
  | [] -> None
  | (i,t)::q -> if i = id then Some(t) else cherche id q 

open TypeVariable

(* fonction permettant d'appliquer les regles d'inference de type 
   expr : expression a typer
   env : environnement associe a expr, ou l'on va faire le typage
   retourne :  le typage de expr, si il y a eu une erreur de typage
   renvoie None, sinon Some(type, eqs) avec type, le type contenant
   des variables fraiches et eqs, la liste des equations obtenues 
   lors de l'application des regles *)
let rec typer : expr -> 'a env -> ('a typ * (('a equ) list )) option = fun expr env -> 
  match expr with
  (*constante*)
  | EConstant(c) -> (match c with
                    | CBooleen(_) -> Some(TBool,[])
                    | CEntier(_) -> Some(TInt,[])
                    | CUnit -> Some(TUnit,[])
                    | CNil -> Some(TList(TUnit),[]))
  (*operation binaire*)
  | EBinop (token) ->  (match token with
                    |CONS -> let a = TVar(fraiche()) in
                              Some(TFun(a,TFun(TList(a),TList(a))),[])
                    |CONCAT -> let a = TVar(fraiche()) in
                              Some(TFun(TList(a),TFun(TList(a),TList(a))),[])
                    |VIRG -> let a1 = TVar(fraiche ()) and a2 = TVar(fraiche ()) in Some(TFun (a2, TProd(a1, a2)), [])
                    | PLUS | MOINS | MULT | DIV -> Some(TFun(TInt,TFun(TInt,TInt)),[])
                    | AND | OR -> Some(TFun(TBool,TFun(TBool,TBool)),[])
                    | EQU | INFEQ | SUPEQ | INF | SUP| NOTEQ -> let a = TVar(fraiche()) in
                                                                Some(TFun(a,TFun(a,TBool)),[])
                    | _ -> None)
  (*identificateur*)
  | EIdent (i) -> (match cherche i env with
                      | Some(t) -> Some(t, [])
                      | None -> None)
  (*produit*)
  | EProd (e1,e2) -> (match (typer e1 env, typer e2 env) with
                      |(Some(t1,eq1), Some(t2,eq2)) -> Some(TProd(t1,t2),eq1@eq2)
                      |_ -> None)
  (*constructeur*)
  | ECons (e1,e2) -> (match (typer e1 env, typer e2 env) with
                      |(Some(t1,eq1), Some(t2,eq2)) -> Some(t2,(t2,TList(t1))::eq1@eq2)
                      |_ -> None)
  (*fonction*)
  | EFun (x,e) -> (let a = TVar(fraiche()) in 
                    match (typer e ((x,a)::env)) with
                      |(Some(t,eq)) -> Some(TFun(a,t),eq)
                      |_ -> None)
  (*expression if then else*)
  | EIf (b,e1,e2) -> (match (typer b env, typer e1 env, typer e2 env) with
                      |(Some(t,eq1), Some(t1,eq2), Some(t2,eq3)) -> Some(t1,(t,TBool)::((t1,t2)::eq1@eq2@eq3))
                      |_ -> None)
  (*application*)
  | EApply (e1,e2) -> (match (typer e1 env, typer e2 env) with
                      |(Some(t1,eq1), Some(t2,eq2)) -> let a = TVar(fraiche()) in
                        Some(a,(t1,TFun(t2,a))::eq1@eq2)
                      |_ -> None)
  (*expression let ... in*)
  | ELet (x,e1,e2) -> (match (typer e1 env) with
                      |(Some(t,eq1)) -> (match (typer e2 ((x,t)::env)) with
                                        |(Some(t',eq2)) -> Some(t',eq1@eq2)
                                        | _ -> None)
                      |_ -> None)
  (*expression let rec ... in*)
  | ELetrec (x,e1,e2) -> (let a = TVar(fraiche()) in
                          match (typer e1 ((x,a)::env), typer e2 ((x,a)::env)) with
                            |(Some(t,eq1), Some(t',eq2)) -> Some(t',(a,t)::eq1@eq2)
                            |_ -> None)
end

(*module de normalisation des types*)
module Normalizer =
struct
open RegleTypage
(*Definition du type jugementNorm compose d'une liste d'equations, et du type de l'expression
   contenant encore des variables fraiches*)
type 'a jugementNorm = JugementNorm of 'a equ list * 'a typ

(* fonction qui remplace le type variable alpha par sa définition tau dans un 'a typ 
   alpha : type variable a remplacer
   tau : type qui doit remplacer alpha
   exp : type dans lequel doit se faire la substitution
   retourne : le type exp actualise *)
let rec substitution : TypeVariable.t -> 'a typ -> 'a typ -> 'a typ = fun alpha tau exp -> 
  match exp with 
  | TVar(x) when x = alpha -> tau
  | TProd(x,y) -> TProd(substitution alpha tau x, substitution alpha tau y)
  | TFun(x,y) -> TFun(substitution alpha tau x, substitution alpha tau y)
  | TList x -> TList (substitution alpha tau x)
  | x -> x

(* fonction qui remplace tous les types variables alpha par leur définition tau dans la liste d'équations 
   alpha : type variable a remplacer
   tau : type qui doit remplacer alpha
   eqs : liste d'equations de type dans lesquelles doivent se faire les substitutions *)
let rec substitutions : TypeVariable.t -> 'a typ -> 'a equ list -> 'a equ list = fun alpha tau eqs ->
  match eqs with
  | [] -> []
  | (e1,e2)::q -> 
    let sub1 = substitution alpha tau e1 in
    let sub2 = substitution alpha tau e2 in
    (sub1,sub2)::(substitutions alpha tau q)

(*fonction qui teste si a est libre dans rho
   a : t
   rho : t typ
   retourne : true si a est libre dans rho, false sinon*)
let rec isFree : TypeVariable.t -> TypeVariable.t typ -> bool = fun a rho ->
  match rho with
  | TInt -> true
  | TBool -> true
  | TUnit -> true
  | TVar(b) -> not(TypeVariable.equal a b)
  | TFun(t1,t2) -> isFree a t1 && isFree a t2
  | TProd(t1,t2) -> isFree a t1 && isFree a t2
  | TList(t) -> isFree a t

(* fonction qui normalise les equations afin d'obtenir le type exact d'une expression 
   parametre : JugementNorm(eqs, tau) avec eqs la liste des equations a normaliser et
   tau le type de l'expression contenant encore des variables fraiches
   retourne : None si il y a une erreur de type, Some(tau) sinon, avec tau le type exact
   de l'expression initiale *)
let rec normalizer : 'a jugementNorm -> 'a typ option = 
  function
  (* {int=int} *)
  | JugementNorm((TInt, TInt)::eqs, tau) -> normalizer (JugementNorm(eqs, tau))
  (* {bool=bool}*)
  | JugementNorm((TBool, TBool)::eqs, tau) -> normalizer (JugementNorm(eqs, tau))
  (* {unit=unit}*)
  | JugementNorm((TUnit, TUnit)::eqs, tau) -> normalizer (JugementNorm(eqs, tau))
  (* {t1 list = t2 list} *)
  | JugementNorm((TList(t1), TList(t2))::eqs, tau) -> normalizer (JugementNorm((t1,t2)::eqs, tau))
  (* {t1->t2 = sigma1->sigma2} *)
  | JugementNorm((TFun(t1,t2), TFun(s1,s2))::eqs, tau) -> normalizer (JugementNorm((t1,s1)::(t2,s2)::eqs, tau))
  (* {t1*t2 = sigma1*sigma2} *)
  | JugementNorm((TProd(t1,t2), TProd(s1,s2))::eqs, tau) -> normalizer (JugementNorm((t1,s1)::(t2,s2)::eqs, tau))
  (* {alpha=alpha} *)
  | JugementNorm((TVar(a), TVar(b))::eqs, tau) when TypeVariable.equal a b -> normalizer (JugementNorm(eqs, tau))
  (* {p=alpha}*)
  | JugementNorm((p, TVar(a))::eqs, tau) -> normalizer (JugementNorm((TVar(a),p)::eqs, tau))
  (* {alpha=p} *)
  | JugementNorm((TVar(a), p)::eqs, tau) when isFree a p -> normalizer (JugementNorm(substitutions a p eqs, substitution a p tau))                                                    
  (* ensemble vide *)
  | JugementNorm([], tau) -> Some(tau)
  (* les equations non presentes ne sont pas normalisables et declenchent une erreur de type *)
  | _ -> None
  
end

(*Definition d'expressions pour les tests*)
module ExpressionsTest =
struct
  let expression1 = ELet ("x" ,EConstant (CEntier 1), EApply (EApply (EBinop PLUS, EIdent "x"), EIdent "y")) (*let x=1 in x + y *)
  let expression2 = EFun ( "" ,ELet ("x" ,EConstant (CEntier 1), EApply (EApply (EBinop PLUS, EIdent "x"), EIdent "y"))) (*fun () -> let x=1 in x + y *)
  let expression3 = EFun ( "y" ,ELet ("x" ,EConstant (CEntier 1), EApply (EApply (EBinop PLUS, EIdent "x"), EIdent "y"))) (*fun y -> let x=1 in x + y *)
  let expression4 = EFun( "y", EIf (EApply (EApply (EBinop EQU, EIdent("y")),EConstant (CEntier 1)), EConstant (CBooleen true), EConstant ( CBooleen false)))
end

(*Exemple d'utilisation du typer*)
let ex = RegleTypage.typer (EIdent("x")) [("x",TInt)]

(*Tests du typer*)
open ExpressionsTest
let t = TypeVariable.fraiche ();;
let%test _ = (RegleTypage.typer expression1 []= None);;
let%test _ = (RegleTypage.typer expression2 []= None);;
let%test _ = (RegleTypage.typer (EIdent("x")) [("x",TInt)] = Some(TInt, []));;
let%test _ = match (RegleTypage.typer expression3 []) with
            | Some( TFun (TVar _, TVar _),[(TVar _,TFun (TVar _,TVar _));(TFun (TInt,TFun (TInt,TInt)),TFun (TInt,TVar _))]) -> true
            |_ -> false

(*Tests du normalizer*)
let%test _ = match RegleTypage.typer expression3 [] with 
| Some(t,q) -> (match Normalizer.normalizer(JugementNorm(q,t)) with
                  |Some( TFun (TInt, TInt)) -> true
                  |_ -> false)
| None -> false
let%test _ = Normalizer.normalizer(JugementNorm([],TInt)) = Some(TInt);;