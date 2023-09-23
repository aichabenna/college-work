(******************************************************************************)
(*                                                                            *)
(* Domaine des signes :                                                       *)
(*                                                                            *)
(*       STop                                                                 *)
(*      / | \                                                                 *)
(*     /  |  \                                                                *)
(*    /  SN0  \                                                               *)
(* SLe0 /   \ SGe0                                                            *)
(*   |\/     \/|                                                              *)
(*   |/\     /\|                                                              *)
(* SLt0 \   / SGt0                                                            *)
(*    \  SE0  /                                                               *)
(*     \  |  /                                                                *)
(*      \ | /                                                                 *)
(*       SBot                                                                 *)
(*                                                                            *)
(* avec pour fonction de concrétisation gamma :                               *)
(* STop |-> Z                                                                 *)
(* SN0  |-> { n \in Z | n /= 0 }                                              *)
(* SLe0 |-> { n \in Z | n <= 0 }                                              *)
(* SGe0 |-> { n \in Z | n >= 0 }                                              *)
(* SLt0 |-> { n \in Z | n < 0 }                                               *)
(* SGt0 |-> { n \in Z | n > 0 }                                               *)
(* SE0  |-> { 0 }                                                             *)
(* SBot |-> \emptyset                                                         *)
(*                                                                            *)
(******************************************************************************)

(* Le treillis est un produit de 3 treillis à deux valeurs, i.e. des booléens *)
(* Chaque booléen représente une direction différente dans ce treillis,       *)
(* en partant de Bot. Tout élément abstrait est défini par un triplet         *)
(* de booléens (tn, t0, tp) qui représentent respectivement:                  *)
(* tn: la présence des nombres négatifs dans la concrétisation                *)
(* t0: la présence du nombre 0 dans la concrétisation                         *)
(* tp: la présence des nombres positifs dans la concrétisation                *)
type t = bool * bool * bool

let fprint ff t = Format.fprintf ff "%s"
  (match t with
    | (false,false,false) -> "⊥"
    | (false,false,true) ->  "SGt0"
    | (false,true,true) ->  "SGe0"
    | (false,true,false) ->  "SE0"
    | (true,false,false) ->  "SLt0"
    | (true,false,true) ->  "SN0"
    | (true,true,false) ->  "SLe0"
    | (true,true,true)    -> "⊤")


let order x y = match x, y with
  | _, (true, true, true) -> true
  | (true,true,true), _ -> false
  | (false,false,false),_ -> true
  | _,(false,false,false) -> false
  | (x1, false,x2),(y1,false,y2) -> (x==y)||(y1&&y2)
  | (x1, true,x2),(y1,true,y2) -> (x==y)||((not x1)&&(not x2))
  | (x1,false,x2),(y1,true,y2) -> (x1=y1)&&(x2=y2)
  | (_,true,_),(_,false,_) -> false

  
let top = (true, true, true)
let bottom = (false, false, false)

(* borne supérieure : plus petit des majorants de {x, y} *)
let join x y = match x,y with
| (true,true,true),_ | _,(true,true,true) -> top
| (false,false,false),_ -> y
| _,(false,false,false) -> x
| (true,false,false),(false,false,true) | (false,false,true),(true,false,false) -> (true,false,true)
| _,_ -> if order x y then y
         else if order y x then x
         else top

(* borne supérieure : plus grand des minorants de {x, y} *)
let meet x y = match x,y with
  (**cas avec top**)
  | (true,true,true),_ -> y
  | _,(true,true,true) -> x
  (**cas avec bottom**)
  | (false,false,false),_ | _,(false,false,false) -> bottom
  (**intersection du haut**)
  | (false,true,true),(true,true,false) | (true,true,false),(false,true,true) -> (false,true,false)
  (**intersection du haut et du bas**)
  | (a,true,b),(c,false,d) -> if (a=c)&&(b=d) then y else bottom
  | (a,false,b),(c,true,d) -> if (a=c)&&(b=d) then x else bottom
  (**autres cas louches**)
  | _ -> bottom

(* Le treillis n'a pas de chaine strictement croissante infinie,
 * donc il suffit d'utiliser l'union comme élargissement. *)
let widening = join

let sem_itv n1 n2 = 
  (**Cas où c'est mal rangé (n1 > n2) **)
  if n1 > n2 then bottom
  (**Cas d'égalité**)
  else if n1 = n2 then (
          (**n1=n2=0**)
          if n1 = 0 then (false,true,false)
          (**n1=n2>0**)
          else if n1 > 0 then (false,false,true)
          (**n1=n2<0**)
          else (true,false,false)
  )
  (**Cas bien rangé et pas égal**)
  else (
          (**0<n1<n2**) 
          if n1>0 then (false,false,true)
          (**0=n1<n2**)
          else if n1 = 0 then (false,true,true)
          (**n1<n2<0**)
          else if n2<0 then (true,false,false)
          (**n1<n2=0**)
          else if n2 = 0 then (true,true,false)
          (**n1<0<n2**)
          else if n1<0 && n2>0 then (true,true,true)
          else top
  )

let sem_plus x y = match x,y with
  | (false,false,false), _ -> bottom
  | _, (false,false,false) -> bottom
  (**Cas ajouter 0**)
  | _, (false,true,false) -> x
  | (false,true,false),_ -> y
  (**Cas somme de 2 >0 ou >=0**)
  | (false,b1,true),(false,b2,true) -> if not b1 || not b2 then (false,false,true) 
                                                          else (false,true,true)
  (**Cas somme de 2 <0 ou <=0**)
  | (true,b1,false),(true,b2,false) -> if not b1 || not b2 then (true,false,false)
                                                          else (true,true,false) 
  | _ -> top

  let sem_minus x y = match x,y with
    | (false, false, false), _ -> bottom
    | _, (false,false,false) -> bottom
    (**Cas soustraire 0**)
    | _, (false,true,false) -> x
    (**Cas d'inversion**)
    | (false,true,false), (a,b,c) -> (not a,b,not c)
    (**Cas pos - neg**)
    |(false,b1,true), (true,b2,false) -> if b1 && b2 then (false, true, true) else (false, false, true)
    (**Cas neg - pos**)
    |(true,b1,false), (false,b2,true) -> if b1 && b2 then (true,true,false) else (true,false, false)
    | _ -> top 

let sem_times x y = match x,y with
  | (false, false, false), _ -> bottom
  | _, (false,false,false) -> bottom
  (**Cas soustraire 0**)
  | _, (false,true,false) -> (false,true,false)
  | (false,true,false),_ -> (false,true,false)
  (**Cas pos * neg ou neg*pos **)
  |(false,b1,true), (true,b2,false) | (true,b1,false), (false,b2,true)-> if not b1 && not b2 then (true,false,false)
                                                                                             else (true,true,false)
  (**Cas pos*pos ou neg*neg **)
  |(false,b1,true), (false,b2,true) | (true,b1,false), (true,b2,false)-> if not b1 && not b2 then (false,false,true)
                                                                                             else (false,true,true)
  | _ -> top

let sem_div x y = match x, y with
  (* À compléter. *)
  (* ...          *)
  | _            -> assert false

let sem_guard = function 
  | (_,_,true) -> (false, false, true)
  | _ -> bottom

let backsem_plus x y r = match x, y, r with
  (* À compléter. *)
  (* ...          *)
  | _            -> (x, y)

let backsem_minus x y r = match x, y, r with
  (* À compléter. *)
  (* ...          *)
  | _            -> (x, y)

let backsem_times x y r = match x, y, r with
  (* À compléter. *)
  (* ...          *)
  | _            -> (x, y)

let backsem_div x y r = match x, y, r with
  (* À compléter. *)
  (* ...          *)
  | _            -> (x, y)
