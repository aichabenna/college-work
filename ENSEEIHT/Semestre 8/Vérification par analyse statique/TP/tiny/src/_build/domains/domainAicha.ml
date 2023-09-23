(* Template to write your own non relational abstract domain. *)

(* To implement your own non relational abstract domain,
 * first give the type of its elements, *)
type t = Top | Bottom | Valeur of int

(* a printing function (useful for debuging), *)
let fprint ff = function
  | Valeur(x) -> Format.fprintf ff "%i" x
  | Top -> Format.fprintf ff "Top"
  | Bottom -> Format.fprintf ff "Bottom"

(* the order of the lattice. *)
let order x y = match x, y with
  | Bottom, _ -> true
  | _, Top -> true
  | Valeur i, Valeur j -> i=j
  | _ -> false

(* and infimums of the lattice. *)
let top = Top
let bottom = Bottom

(* All the functions below are safe overapproximations.
 * You can keep them as this in a first implementation,
 * then refine them only when you need it to improve
 * the precision of your analyses. *)

let join x y = match x, y with
  | Bottom, v | v, Bottom -> v
  | _, Top | Top, _ -> Top
  | Valeur i, Valeur j -> if i==j then Valeur i else Top

let meet x y = match x, y with
  | Bottom, _ | _, Bottom -> Bottom
  | v, Top | Top, v -> v
  | Valeur i, Valeur j -> if i==j then Valeur i else Bottom

let widening = join  (* Ok, maybe you'll need to implement this one if your
                      * lattice has infinite ascending chains and you want
                      * your analyses to terminate. *)

let sem_itv n1 n2 = 
  if n1 < n2 then Top
  else if n1=n2 then Valeur n1
  else Bottom

let sem_plus x y = match x, y with 
  | Valeur i, Valeur j -> Valeur (i+j)
  | Bottom, _ | _, Bottom -> Bottom
  | Top, _ | _, Top -> Top

let sem_minus x y = match x, y with 
  | Valeur i, Valeur j -> Valeur (i-j)
  | Bottom, _ | _, Bottom -> Bottom
  | Top, _ | _, Top -> Top

let sem_times x y = match x, y with 
  | Valeur i, Valeur j -> Valeur (i*j)
  | Bottom, _ | _, Bottom -> Bottom
  | Top, _ | _, Top -> Top

let sem_div x y = match x, y with 
  | Valeur i, Valeur j -> Valeur (i*j)
  | Bottom, _ | _, Bottom -> Bottom
  | Top, _ | _, Top -> Top

let sem_guard = function
 | Bottom -> Bottom
  | Top -> Top
  | (Valeur i) as c -> if i > 0 then c else Bottom

let backsem_plus x y r = x, y
let backsem_minus x y r = x, y
let backsem_times x y r = x, y
let backsem_div x y r = x, y
