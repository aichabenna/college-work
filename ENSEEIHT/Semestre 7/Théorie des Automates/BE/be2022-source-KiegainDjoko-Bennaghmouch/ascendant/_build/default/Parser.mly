%{

(* Partie recopiee dans le fichier CaML genere. *)
(* Ouverture de modules exploites dans les actions *)
(* Declarations de types, de constantes, de fonctions, d'exceptions exploites dans les actions *)

%}

/* Declaration des unites lexicales et de leur type si une valeur particuliere leur est associee */

(* A COMPLETER *)
%token <int> UL_ENTIER
%token <string> UL_IDENT
%token UL_PAROUV
%token UL_PARFER
%token UL_POINT

/* Defini le type des donnees associees a l'unite lexicale */

(* A COMPLETER *)

/* Unite lexicale particuliere qui represente la fin du fichier */

%token UL_FIN

/* Type renvoye pour le nom terminal document */
%type <unit> scheme

/* Le non terminal document est l'axiome */
%start scheme

%% /* Regles de productions */
(** scheme  = programme *)
scheme : s_expression UL_FIN { (print_endline "programme : S-expression UL_FIN ") }

s_expression : s_expression_parenthese { (print_endline "S-expression : expression UL_FIN ") }
                | UL_IDENT { (print_endline "S-expression : expression UL_FIN ") }
                | UL_ENTIER { (print_endline "S-expression : expression UL_FIN ") }

expression_parenthesee : s_expression UL_POINT s_expression { (print_endline "S-expression : expression UL_FIN ") }
                        | s_expression_boucle { (print_endline "S-expression : expression UL_FIN ") }

s_expression_boucle : /*lamnda vide*/ { (print_endline "programme : S-expression UL_FIN ") }
                    | s_expression s_expression_boucle { (print_endline "S-expression : expression UL_FIN ") }

s_expression_parenthese : UL_PAROUV expression_parenthesee UL_PARFER { (print_endline "S-expression : expression UL_FIN ") }


%%

