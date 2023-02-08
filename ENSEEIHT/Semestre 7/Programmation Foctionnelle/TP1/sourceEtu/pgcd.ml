(*  Exercice à rendre **)
(*  pgcd : int -> int -> int
    Calcule le PGCD de deux nombres entiers passes en parametres.
    Parametre a: int, premier entier
    Parametre b: int, second entier
    Preconditions: (a!=0 || b!=0) && (a>=0 && b>=0)
    Resultat : int, PGCD de a et b
*)

let rec pgcd a b =
  if a = b then a
  else if a > b then pgcd (a - b) b
  else pgcd a (y - a)

(*  TO DO : tests unitaires *)
let%test _ = pgcd 32 14 = 2
let%test _ = pgcd 12 15 = 3 
let%test _ = pgcd 6 6 = 6
let%test _ = pgcd 3 2 = 1

(*  Exercice à rendre **)
(*  pgcd_v2 : int * int -> int
    Calcule le PGCD de deux nombres entiers passes en parametres.
    Parametre (a, b): int * int, 
    Preconditions: (a!=0 || b!=0) && (a>=0 && b>=0)
    Resultat : int, PGCD de a et b
*)

let rec pgcd_v2 (a, b) =
  if a = b then a
  else if a > b then pgcd_v2 ((a - b), b)
  else pgcd_v2 (a, (b - a))

(*  TO DO : tests unitaires *)
let%test _ = pgcd_v2 (32, 14) = 2
let%test _ = pgcd_v2 (12, 15) = 3 
let%test _ = pgcd_v2 (6, 6) = 6
let%test _ = pgcd_v2 (3, 2) = 1


(*  Exercice à rendre **)
(*  on leve cette condition (a>=0 && b>=0) en utilisant abs *)
(*  pgcd_v3 : int * int -> int
    Calcule le PGCD de deux nombres entiers passes en parametres.
    Parametre (a, b): int * int, 
    Preconditions: (a!=0 || b!=0)
    Resultat : int, PGCD de a et b
*)

let rec pgcd_v3 (a, b) =
  if abs a = abs b then abs a
  else if abs a > abs b then pgcd_v3 ((abs a - abs b), abs b)
  else pgcd_v3 (abs a, (abs b - abs a))

(*  TO DO : tests unitaires *)
let%test _ = pgcd_v3 (32, 14) = 2
let%test _ = pgcd_v3 (12, 15) = 3 
let%test _ = pgcd_v3 (6, 6) = 6
let%test _ = pgcd_v3 (3, 2) = 1
let%test _ = pgcd_v3 (-2, -3) = 1
let%test _ = pgcd_v3 (-2, -4) = 2