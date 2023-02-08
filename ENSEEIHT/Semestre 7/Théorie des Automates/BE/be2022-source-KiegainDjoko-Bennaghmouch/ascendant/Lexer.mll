{

(* Partie recopiée dans le fichier CaML généré. *)
(* Ouverture de modules exploités dans les actions *)
(* Déclarations de types, de constantes, de fonctions, d'exceptions exploités dans les actions *)

  open Parser 
  exception LexicalError

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

rule lexer = parse
  | ['\n' '\t' ' ']+					{ (lexer lexbuf) }
  | commentaire						{ (lexer lexbuf) }
(* A COMPLETER *)
  | Ident           as texte   { UL_IDENT (texte) }
  | entier          as texte   { UL_ENTIER (int_of_string texte) }
  | "("                          { UL_PAROUV }
  | ")"                          { UL_PARFER }
  | "."                          { UL_POINT }
  | eof							{ UL_FIN }
  | _ as texte				 		{ (print_string "Erreur lexicale : ");(print_char texte);(print_newline ()); raise LexicalError }

{

}
