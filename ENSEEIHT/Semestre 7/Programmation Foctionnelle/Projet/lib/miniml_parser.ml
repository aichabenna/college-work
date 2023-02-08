open Miniml_types
open Miniml_lexer
open Miniml_printer
open Lazyflux

module FluxEnt = Flux;;
module Solution = Flux;;
(* Fonction de lecture d'un fichier.    *)
(* Produit le flux des lexèmes reconnus *)
let read_miniml_tokens_from_file filename : token FluxEnt.t =
  try
    let chan = open_in filename in
    let buf = Lexing.from_channel chan in
    line_g := 1;
    let next_token () =
      try
        let next = token buf in
        if next = EOF
        then
          begin
            close_in chan;
            None
          end
        else
          Some (next, ())
   with
   | ErreurLex msg ->
      begin
        close_in chan;
        raise (ErreurLecture (Format.sprintf "ERREUR : ligne %d, lexème '%s' : %s" !line_g (Lexing.lexeme buf) msg))
      end in
    Flux.unfold next_token ()
 with
    | Sys_error _ -> raise (ErreurLecture (Format.sprintf "ERREUR : Impossible d'ouvrir le fichier '%s' !" filename))
;;

(* Fonction de lecture d'un buffer.   *)
(* Similaire à la fonction précédente *)
let read_miniml_tokens_from_lexbuf buf : token FluxEnt.t =
  line_g := 1;
  let next_token () =
    try
      let next = token buf in
      if next = EOF
      then
        begin
          None
        end
      else
        Some (next, ())
    with
    | ErreurLex msg ->
       begin
         raise (ErreurLecture (Format.sprintf "ERREUR : ligne %d, lexème '%s' : %s" !line_g (Lexing.lexeme buf) msg))
       end in
  Flux.unfold next_token ()
;;

(* Fonction de lecture d'une chaîne.  *)
(* Similaire à la fonction précédente *)
let read_miniml_tokens_from_string chaine : token FluxEnt.t =
  read_miniml_tokens_from_lexbuf (Lexing.from_string chaine)
;;

(* types des parsers *)
type ('a,'b) result = ('b * 'a FluxEnt.t) Solution.t;;
type ('a, 'b) parser = 'a FluxEnt.t -> ('a, 'b) result;;

(* interface des parsers: combinateurs de parsers et parsers simples *)
module type Parsing =
  sig
    val map : ('b -> 'c) -> ('a, 'b) parser -> ('a, 'c) parser

    val return : 'b -> ('a, 'b) parser

    val ( >>= ) : ('a, 'b) parser -> ('b -> ('a, 'c) parser) -> ('a, 'c) parser

    val zero : ('a, 'b) parser

    val ( ++ ) : ('a, 'b) parser -> ('a, 'b) parser -> ('a, 'b) parser

    val run : ('a, 'b) parser -> 'a FluxEnt.t -> 'b Solution.t

    val pvide : ('a, unit) parser

    val ptest : ('a -> bool) -> ('a, 'a) parser

    val ( *> ) : ('a, 'b) parser -> ('a, 'c) parser -> ('a, 'b * 'c) parser
  end

(* implantation des parsers, comme vu en TD. On utilise les opérations *)
(* du module Flux et du module Flux                                *)
module Parser : Parsing =
  struct
    let map fmap parse f = Solution.map (fun (b, f') -> (fmap b, f')) (parse f);; 

    let return b f = Solution.return (b, f);;

    let (>>=) parse dep_parse = fun f -> Solution.(parse f >>= fun (b, f') -> dep_parse b f');;

    let zero _ = Solution.zero;;

    let (++) parse1 parse2 = fun f -> Solution.(parse1 f ++ parse2 f);;

    let run parse f = Solution.(map fst (filter (fun (_, f') -> Flux.uncons f' = None) (parse f)));;

    let pvide f =
      match Flux.uncons f with
      | None   -> Solution.return ((), f)
      | Some _ -> Solution.zero;;

    let ptest p f =
      match Flux.uncons f with
      | None        -> Solution.zero
      | Some (t, q) -> if p t then Solution.return (t, q) else Solution.zero;;

    let ( *> ) parse1 parse2 = fun f ->
      Solution.(parse1 f >>= fun (b, f') -> parse2 f' >>= fun (c, f'') -> return ((b, c), f''));;
  end

(* Fonctions auxiliaires de traitement des lexèmes *)
(* contenant une information: IDENT, BOOL et INT   *)
let isident =
  function IDENT _     -> true
         | _           -> false
let isbool =
  function BOOL _      -> true
         | _           -> false
let isint =
  function INT _       -> true
         | _           -> false

let unident =
  function
  | IDENT id    -> id
  | _           -> assert false
let unbool =
  function
  | BOOL b      -> b
  | _           -> assert false   
let unint =
  function
  | INT i       -> i
  | _           -> assert false

open Parser

let drop p = map (fun _ -> ()) p;;

(* Fonctions de parsing de MiniML *)
(* Parser fin de fichier *)
let p_eof = pvide;;

(* Parsers pour les mots cles*)
let p_token t = drop (ptest ((=) t));;
let p_let = p_token LET
let p_in = p_token IN
let p_rec = p_token REC
let p_paro = p_token PARO
let p_parf = p_token PARF
let p_if = p_token IF
let p_else = p_token ELSE
let p_then = p_token THEN
let p_fun = p_token FUN
let p_to = p_token TO
let p_equ = p_token EQU
let p_concat = p_token CONCAT
let p_cons = p_token CONS
let p_moins = p_token MOINS
let p_plus = p_token PLUS
let p_mult = p_token MULT
let p_div = p_token DIV
let p_and = p_token AND
let p_or = p_token OR
let p_croo = p_token CROO
let p_crof = p_token CROF
let p_noteq = p_token NOTEQ
let p_infeq = p_token INFEQ
let p_supeq = p_token SUPEQ
let p_sup = p_token SUP
let p_inf = p_token INF
let p_ident = ptest isident
let p_int = ptest isint
let p_bool = ptest isbool

(* Grammaire des expressions de MiniML *)

(* 1. Expr -> let Liaison in Expr *)
(* 2. Expr -> let rec Liaison in Expr *)
(* 3. Expr -> (Expr Binop Expr) *)
(* 4. Expr -> (Expr) *)
(* 5. Expr -> (Expr Expr) *)
(* 6. Expr -> if Expr then Expr else Expr *)
(* 7. Expr -> (fun ident -> Expr) *)
(* 8. Expr -> ident *)
(* 9. Expr -> Constant *)

(* 10. Liaison -> ident = Expr *)
(* 11. Binop -> Arithop | Boolop | Relop | @ | :: *)
(* 12. Arithop -> + | - | * | / *)
(* 13. Boolop -> && | || *)
(* 14. Relop -> = | <> | <= | < | >= | > *)
(* 15. Constant -> entier | booléen | [] | () *)

(* tokens : flux de tokens de l'expression *)
(* (token, expr) parser *)
let rec parseExpr = fun tokens ->
  (
    (* 1. Expr -> let Liaison in Expr *)
    (p_let >>= fun () ->
    parseLiaison >>= fun l ->
    p_in >>= fun () ->
    parseExpr >>= fun e ->
      let (id, expr) = l in
        return (ELet (id, expr, e)))
    ++
    (* 2. Expr -> let rec Liaison in Expr *)
    (p_let >>= fun () ->
    p_rec >>= fun () ->
    parseLiaison >>= fun l ->
    p_in >>= fun () ->
    parseExpr >>= fun e ->
      let (id, expr) = l in
        return (ELetrec(id, expr, e)))
    ++
    (* 3. Expr -> (Expr Binop Expr) *)
    (p_paro >>= fun ()->
    parseExpr >>= fun e1 ->
    parseBinop >>= fun b ->
    parseExpr  >>= fun e2 ->
    p_parf >>= fun () ->
      return (EApply(EApply(b,e1), e2))) (*PAS SURE DU TOUT*)
    ++
    (* 4. Expr -> (Expr) *)
    (p_paro >>= fun () ->
    parseExpr >>= fun e ->
    p_parf >>= fun () ->
      return e)
    ++
    (* 5. Expr -> (Expr Expr) *)
    (p_paro >>= fun () ->
    parseExpr >>= fun e1 ->
    parseExpr >>= fun e2 ->
    p_parf >>= fun () ->
      return (EProd (e1,e2))) (*PAS SURE NON PLUS*)
    ++
    (* 6. Expr -> if Expr then Expr else Expr *)
    (p_if >>= fun () ->
    parseExpr >>= fun e1 ->
    p_then >>= fun () ->
    parseExpr >>= fun e2 ->
    p_else >>= fun () ->
    parseExpr >>= fun e3 ->
      return (EIf(e1, e2, e3)))
    ++
    (* 7. Expr -> (fun ident -> Expr) *)
    (p_paro >>= fun () ->
    p_fun >>= fun () ->
    p_ident >>= fun i -> (*pas sure de l'utilisation de unident*)
    p_to >>= fun () ->
    parseExpr >>= fun e ->
    p_parf >>= fun () ->
      return (EFun(unident i, e)))
    ++
    (* 8. Expr -> ident *)
    (p_ident >>= fun i ->
      return (EIdent(unident i)))
    ++
    (* 9. Expr -> Constant *)
    (parseConstant >>= fun c ->
      return c)
  ) tokens

(* 10. Liaison -> ident = Expr *)
and parseLiaison = fun tokens ->
  (p_ident >>= fun i ->
  p_equ >>= fun () ->
  parseExpr >>= fun e ->
    return (unident i, e)) tokens

(* 11. Binop -> Arithop | Boolop | Relop | @ | :: *)
and parseBinop = fun tokens ->
  ((parseArithop >>= fun o ->
    return (EBinop(o)))
    ++
    (parseBoolop >>= fun b ->
      return (EBinop(b)))
    ++
    (parseRelop >>= fun r ->
      return (EBinop(r)))
    ++
    (p_concat >>= fun () ->
      return (EBinop(CONCAT)))
    ++
    (p_cons >>= fun () ->
      return (EBinop(CONS)))
  ) tokens

(* 12. Arithop -> + | - | * | / *)
and parseArithop = fun tokens ->
  ((p_plus >>= fun () ->
      return PLUS)
    ++
    (p_moins >>= fun () ->
      return MOINS)
    ++
    (p_mult >>= fun () ->
      return MULT)
    ++
    (p_div >>= fun () ->
      return DIV)
  ) tokens

(* 13. Boolop -> && | || *)
and parseBoolop = fun tokens ->
  ((p_and >>= fun () ->
      return AND)
    ++
    (p_or >>= fun () ->
      return OR)
  ) tokens

(* 14. Relop -> = | <> | <= | < | >= | > *)
and parseRelop = fun tokens ->
  ((p_equ >>= fun () ->
    return EQU)
    ++
    (p_noteq >>= fun () ->
      return NOTEQ)
    ++
    (p_infeq >>= fun () ->
      return INFEQ)
    ++
    (p_inf >>= fun () ->
      return INF)
    ++
    (p_supeq >>= fun () ->
      return SUPEQ)
    ++
    (p_sup >>= fun () ->
      return SUP)
  ) tokens

(* 15. Constant -> entier | booléen | [] | () *)
  and parseConstant = fun tokens ->
    ((p_int >>= fun i ->
      return (EConstant(CEntier(unint i))))
      ++
      (p_bool >>= fun b ->
        return (EConstant(CBooleen(unbool b))))
      ++
      (p_croo >>= fun () ->
      p_crof >>= fun () ->
        return (EConstant(CNil)))
      ++
      (p_paro >>= fun () ->
      p_parf >>= fun () ->
        return (EConstant(CUnit)))
    ) tokens

(* fonction principale de parsing des programmes LOGO *)
let parse_miniml flux = run (map fst (parseExpr *> p_eof)) flux;;

(* fonctions auxiliaires *)
let miniml_to_string p =
  print_expr Format.std_formatter p
(* flux construit à partir des caractères de la chaîne s *) 
let flux_of_string s =
  Flux.unfold (fun (i, l) -> if i = l then None else Some (s.[i], (i+1, l))) (0, String.length s);;

  (* affichage des programmes LOGO solutions du parsing *)
let rec print_solutions progs =
  match Solution.uncons progs with
  | None        -> ()
  | Some (p, q) ->
    begin
      Format.fprintf Format.std_formatter "Miniml program recognized: " ; 
      miniml_to_string p;
      print_solutions q
    end;;

 (*programmes de test*)
 let test_parser () =
  let rec loop () =
    Format.printf "\n programme?@.";
    flush stdout;
    let l = read_line () in
    let f = read_miniml_tokens_from_string l in
    let progs = parse_miniml f in
    match Solution.uncons progs with
    | None        -> (Format.printf "** parsing failed ! **@."; loop ())
    | Some (p, q) ->
      begin
        print_solutions (Solution.cons p q);
        loop ()
      end
  in loop ();;

 (*let test_constant = 
  let f1 = "1"
  let f2 = "true"
  let f3 = "false"
  let f4 = "[]"
  let f5 = "()"
 let test_liaison = 
  let f = "x = 1" in

let test_expr =
  let f1 = "let x = 3 in (x)"
  let f2 = "let rec y = (fun x -> x+4) in (y 6)"*)

