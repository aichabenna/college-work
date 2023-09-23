(* Template to write your own non relational abstract domain. *)

(* To implement your own non relational abstract domain,
 * first give the type of its elements, *)
type t = Bot | Itv of int option * int option

(* a printing function (useful for debuging), *)
let fprint ff = function
  |Itv (None, None) -> Format.fprintf ff "]-inf, +inf"
  |Itv (None, (Some n)) -> Format.fprintf ff "]-inf, %d[" n
  |Itv ((Some n), None) -> Format.fprintf ff "]%d, -inf[" n
  |Itv ((Some n1), (Some n2)) -> Format.fprintf ff "]%d, %d[" n1 n2
  |Bot -> Format.fprintf ff "Ensemble Vide"

(* Extension de <= `a Z U {-oo}. *)
let leq_minf x y = match x, y with
| None, _ -> true (* -oo <= y *)
| _, None -> false (* x > -oo (x != -oo) *)
| Some x, Some y -> x <= y

(* Extension de <= `a Z U {+oo}. *)
let leq_pinf x y = match x, y with
| _, None -> true (* x <= +oo *)
| None, _ -> false (* +oo > y (y != +oo) *)
| Some x, Some y -> x <= y

let mk_itv o1 o2 = match o1, o2 with
| None, _ | _, None -> Itv (o1, o2)
| Some n1, Some n2 -> if n1 > n2 then Bot else Itv (o1, o2)

(* the order of the lattice. *)
let order x y = match x, y with
  | Bot, _ -> true
  | _, Bot -> false
  | Itv (a, b), Itv (c, d) -> leq_minf c a && leq_pinf b d

(* and infimums of the lattice. *)
let top = Itv (None,None)
let bottom = Bot

(* All the functions below are safe overapproximations.
 * You can keep them as this in a first implementation,
 * then refine them only when you need it to improve
 * the precision of your analyses. *)

let join x y = match x, y with
  | Bot, c | c, Bot -> c
  | Itv (a, b), Itv (c, d) -> Itv
    ((if leq_minf a c then a else c),  
     (if leq_pinf b d then d else b))  

let meet x y = match x, y with
  | Bot, _ | _, Bot -> Bot
  | Itv (a, b), Itv (c, d) -> mk_itv
    (if leq_minf a c then c else a)  
    (if leq_pinf b d then b else d) 

let widening x y = match x,y with
  |Bot,c | c, Bot -> c
  |Itv (a, b), Itv (c, d) -> if ( leq_minf a c ) 
                            then (if not (leq_pinf b d) then Itv (a, b) else Itv (a, None)) 
                            else (if not (leq_pinf b d) then Itv (None, b) else Itv (None, None))

let sem_itv n1 n2 = mk_itv (Some n1) (Some n2)


(******************************************************************)
let add x y = match x, y with
  |None, y -> None (* -oo <= y*)
  |x, None -> None (*x > +oo *)
  |Some x, Some y -> Some(x + y)

let minus x y = match x, y with
  |None, y -> None (* -oo <= y*)
  |x, None -> None (*x > +oo *)
  |Some x, Some y -> Some(x - y)

let times x y = match x, y with
  |None, y -> None (* -oo <= y*)
  |x, None -> None (* x > +oo *)
  |Some x, Some y -> Some(x * y)

let div x y = match x, y with
  |None, b -> None (* -oo <= y*)
  |a, None -> None (*x > +oo *)
  |Some a, Some b -> if Some(b) = Some(0) then None else Some(a / b)

let min_inf x y = match x, y with
  |None, _ | _, None -> None 
  |a, b -> if leq_minf a b then a else b

let max_inf x y = match x, y with
  |None, _ | _, None -> None 
  |a, b -> if leq_pinf a b then a else b

(******************************************************************)

let sem_plus x y = 
  match x, y with
  | Bot, c | c, Bot -> c
  | Itv(a,b), Itv(c,d) -> Itv ((add a c), (add b d))

let sem_minus x y = 
  match x, y with
  | Bot, c | c, Bot -> c
  | Itv(a,b), Itv(c,d) -> Itv ((minus a c), (minus b d))


let sem_times x y = 
  match x, y with
  | Bot, c | c, Bot -> c
  | Itv(a,b), Itv(c,d) -> Itv( (min_inf (min_inf (min_inf (times a b) (times b d) ) (times b c)) (times a d)), 
                              (max_inf (max_inf (max_inf (times a b) (times b d) ) (times b c)) (times a d)) )

let sem_div x y = 
  match x, y with
  | Bot, c | c, Bot -> c
  | Itv(a,b), Itv(c,d) -> Itv( (min_inf (min_inf (min_inf (div a b) (div b d) ) (div b c)) (div a d)), 
                              (max_inf (max_inf (max_inf (div a b) (div b d) ) (div b c)) (div a d)) )

let sem_guard = meet (Itv (Some 1, None))

let backsem_plus x y r = meet x (sem_minus r y), meet y (sem_minus r x)

let backsem_minus x y r = meet x (sem_plus r y), meet y (sem_minus x r)

let backsem_times x y r = meet x (sem_div r y), meet y (sem_div r x)

let backsem_div x y r = meet x (sem_times r y), meet y (sem_times r x)
