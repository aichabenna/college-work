(* ouverture de la "library" definie dans lib/dune *)
open Miniml

(* ouverture de modules de la library Miniml *)
open Miniml_parser
open Miniml_typer
open Miniml_printer

(* ******** à compléter ********* *)

module Main =
  struct
  (*
  Definir enfin un programme principal qui :
  - lit un programme MINIML dans un fichier
  - typer défini dans le module RegleTypage : applique les regles de typage afin d’obtenir son type 
  - normalizer défini dans le module Normalizer : applique les equations associees
  - determine la forme la plus generale des solutions ou l’absence de solution
  - puis affiche le type obtenu ou une erreur de typage.
  *)
  let principal filename = 
    let rec typage expr =
      match Solution.uncons expr with
      | Some(p,q) -> (*Parsing : le type de retour du parseur *)
                (*print_expr Format.std_formatter p; Format.fprintf Format.std_formatter "\n";*)
                (*let typageExpr = RegleTypage.typer p [] in*)
                (match (RegleTypage.typer p []) with (* Environment is a list*)
                  | Some(typ, l) -> (* Normalizer *) 
                              (*let normalizerExpr = Normalizer.normalizer (JugementNorm(l,typ)) in *)
                              (match (Normalizer.normalizer (JugementNorm(l,typ))) with
                                | Some(leType) -> (*affichage d'un type : TypeVariable.fprintf défini dans miniml_typer *) 
                                            print_typ TypeVariable.fprintf Format.std_formatter leType ; 
                                            Format.fprintf Format.std_formatter "\n" ; typage q
                                | None -> Format.fprintf Format.std_formatter "Erreur de type! (Normalisation failed)\n" 
                              )
                  | None -> Format.fprintf Format.std_formatter "Erreur de type! (Typage failed)\n" 
                )
                (*Format.fprintf Format.std_formatter "\n" ; typage q*)
      | None -> Format.fprintf Format.std_formatter "\n---------------------------------------\n" 
    in typage (parse_miniml (read_miniml_tokens_from_file filename))

end

(* Nous allons tester en utilisant un fichier *)
(* il faut donc utiliser la fonction suivante *)
(* read_miniml_tokens_from_file *)
(* Fonction de lecture d'un fichier.    *)
(* Produit le flux des lexèmes reconnus *)

let () = 
  print_endline("\n------------- Tests MiniML -------------\n");
  Main.principal (*"tests/testfile1"*) (Sys.argv.(1)) 
  (* test/testfile* *)

(* On peut également programmer un main qui prend directement une expression*)
(* en ligne de commande à l'aide de la fonction : read_miniml_tokens_from_lexbuf *)
(* Fonction de lecture d'un buffer *)
