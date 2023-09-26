/****************************************************************/
/****************** N7DP : Miniprojet Prolog ********************/
/************************** 21 AVRIL ****************************/
/****************************************************************/
/** Aicha BENNAGHMOUCH ******************************************/
/** Yvan Charles KIEGAIN DJOKO **********************************/
/************************************************ GROUPE L3 *****/
/****************************************************************/

/* Question 1 */
/* représenter la situation initiale grâce à un prédicat. */
:- dynamic(x_on_y/2).

x_on_y(b, c).
x_on_y(a, b).
x_on_y(c, table).

/* Question 2 */
/****************************************************************/
/* Action atomique put_on(X,Y)
 * supposons que X était disposé sur un certain objet Z
 * Préconditions: 
    * X doit être libre pour pouvoir la bouger c-a-d sans aucun 
    objet par dessus sauf la table qui est toujours libre
    * Y doit être libre pour pouvoir la bouger c-a-d sans aucun 
    objet par dessus sauf la table qui est toujours libre
    * X et Y ne doivent pas désigner le même objet (one ne peut 
    poser a sur a par exemple) 
 * Postconditions: 
    * X doit-être sur Y (x_on_y(X,Y))
    * X n'est plus posé sur Z
 */
/****************************************************************/

/* Question 3 */
dispo(table).
dispo(X) :- \+ x_on_y(Z, X).

/* Question 4 */
/* put_on(X, Y) :- X\=Y  , dispo(X), dispo(Y),  x_on_y(X, A), retract(x_on_y(X,A)), assertz(x_on_y(X,Y)).*/

/* Question 5 */
put_on(X, Y) :- X\=Y  , dispo(X), dispo(Y),  x_on_y(X, A), retract(x_on_y(X,A)), assertz(x_on_y(X,Y)), assertz(move(X,Y)).

/* Question 6 */
/***************************************************************
 * put_on(a,table).                 -> yes
    * listing(move).
        move(a, table).
 * put_on(c,a)                      -> no
    * listing(move).
        move(a, table).
 * put_on(b,table), put_on(c,a).    -> yes
    * listing(move).
        move(a, table).
        move(b, table).
        move(c, a).
****************************************************************/

/* Question 7 */

clear(X) :- X\=table, dispo(X).
clear(X) :- X\=table, x_on_y(Y,X), clear(Y), put_on(Y, table).

r_put_on(X,Y) :- clear(X), clear(Y), put_on(X,Y), !.

/* Question 8 */
/* a */
achieve([]) :- listing(move).
achieve([T|Q]) :- T=on(X,Y), r_put_on(X,Y), achieve(Q).

/* b */
/***************************************************************
| ?- achieve([on(a,c), on(c,b)]).                                                                                 
    move(a, table).
    move(b, table).
    move(a, c).
    move(a, table).
    move(c, b).
    (1 ms) yes

Lors de l'évaluation, on retrouve successivement les situations 
de notre liste. Mais on remarque qu'on aurait pu les avoir en 
même temps si on avait réalisé le 2ème but avant le 1er.
****************************************************************/

/* c */
/***************************************************************
On devrait trier de sorte qu'une exécution devra être exécuté 
après que toutes celles qui possèdent comme terme de gauche son 
terme de droite.
****************************************************************/