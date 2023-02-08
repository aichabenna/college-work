{

(* Partie recopiée dans le fichier CaML généré. *)
(* Ouverture de modules exploités dans les actions *)
(* Déclarations de types, de constantes, de fonctions, d'exceptions exploités dans les actions *)

  open Tokens 
  exception Printf

}

(* Déclaration d'expressions régulières exploitées par la suite *)
let chiffre = ['0' - '9']
let minuscule = ['a' - 'z']
let majuscule = ['A' - 'Z']
let alphabet = minuscule | majuscule
let alphanum = alphabet | chiffre | '_'
let commentaire =
  (* Commentaire fin de ligne *)
  "#" [^'\n']*

let Ident = (['A' - 'Z']['a' - 'z''A' - 'Z'] * ) +
let entier = '0' | (['1' - '9']['0' - '9'] * )

rule scanner = parse
  | ['\n' '\t' ' ']+					{ (scanner lexbuf) }
  | commentaire						{ (scanner lexbuf) }
  (* A COMPLETER *)
  | Ident        as texte    { UL_IDENT (texte)::(scanner lexbuf)}
  | entier       as texte    { UL_ENTIER (int_of_string texte)::(scanner lexbuf)}
  | "("                          { UL_PAROUV::(scanner lexbuf) }
  | ")"                          { UL_PARFER::(scanner lexbuf) }
  | "."                          { UL_POINT::(scanner lexbuf)}
  | eof							{ [UL_FIN] }
  | _ as texte				 		{ (print_string "Erreur lexicale : ");(print_char texte);(print_newline ()); (UL_ERREUR::(scanner lexbuf)) }

{

}
