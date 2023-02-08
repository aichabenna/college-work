open Tokens

(* Type du résultat d'une analyse syntaxique *)
type parseResult =
  | Success of inputStream
  | Failure
;;

(* accept : token -> inputStream -> parseResult *)
(* Vérifie que le premier token du flux d'entrée est bien le token attendu *)
(* et avance dans l'analyse si c'est le cas *)
let accept expected stream =
  match (peekAtFirstToken stream) with
    | token when (token = expected) ->
      (Success (advanceInStream stream))
    | _ -> Failure
;;

let acceptIdent stream =
  match (peekAtFirstToken stream) with
    | (UL_IDENT _) -> (Success (advanceInStream stream))
    | _ -> Failure
;;

let acceptEntier stream =
  match (peekAtFirstToken stream) with
    | (UL_ENTIER _) -> (Success (advanceInStream stream))
    | _ -> Failure
;;


(* Définition de la monade  qui est composée de : *)
(* - le type de donnée monadique : parseResult  *)
(* - la fonction : inject qui construit ce type à partir d'une liste de terminaux *)
(* - la fonction : bind (opérateur >>=) qui combine les fonctions d'analyse. *)

(* inject inputStream -> parseResult *)
(* Construit le type de la monade à partir d'une liste de terminaux *)
let inject s = Success s;;

(* bind : 'a m -> ('a -> 'b m) -> 'b m *)
(* bind (opérateur >>=) qui combine les fonctions d'analyse. *)
(* ici on utilise une version spécialisée de bind :
   'b  ->  inputStream
   'a  ->  inputStream
    m  ->  parseResult
*)
(* >>= : parseResult -> (inputStream -> parseResult) -> parseResult *)
let (>>=) result f =
  match result with
    | Success next -> f next
    | Failure -> Failure
;;


(* parseS : inputStream -> parseResult *)
(* Analyse du non terminal Programme *)
let rec parseS stream =
  (print_string "S -> ");
  (match (peekAtFirstToken stream) with
    (* A COMPLETER *)
    | UL_PAROUV -> 
      (print_string "( ");
      (inject stream >>=
    accept UL_PAROUV >>=
    parseX >>=
    accept UL_PARFER )
    | UL_IDENT _ -> 
      (print_string "ident ");
      (inject stream >>=
    acceptIdent)
    | UL_ENTIER _ -> 
      (print_string "entier ");
      (inject stream >>=
    acceptEntier)
    | _ -> Failure)

and parseX stream =
(print_string "X -> ");
  (match (peekAtFirstToken stream) with
    (* A COMPLETER *)
    | UL_PARFER ->(print_string ") "); Success stream
    | UL_PAROUV | UL_IDENT _ | UL_ENTIER _ -> 
      (print_string "( ident entier ");
      (inject stream >>=
    parseS >>=
    parseY)
    | _ -> Failure)

and parseY stream =
(print_string "Y -> ");
  (match (peekAtFirstToken stream) with
    (* A COMPLETER *)
    | UL_POINT -> 
      (print_string ". ");
      (inject stream >>=
    accept UL_POINT >>=
    parseS )
    | UL_PAROUV | UL_IDENT _ | UL_ENTIER _ | UL_PARFER-> 
      (print_string "( ident entier ) ");
      (inject stream >>=
    parseL )
    | _ -> Failure)

and parseL stream =
(print_string "L -> ");
  (match (peekAtFirstToken stream) with
    (* A COMPLETER *)
    | UL_PAROUV | UL_IDENT _ | UL_ENTIER _ -> 
      (print_string "( ident entier ");
      (inject stream >>=
    parseS >>=
    parseL )
    | UL_PARFER -> (print_string ") ");Success stream
    | _ -> Failure)
;;
