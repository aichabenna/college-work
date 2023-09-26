% 2SNL Informatique -- PDL/PPC
% Donnees et predicats pour le TP2
% 2020/2021
% Nicolas Barnier

%Membre du projet : Yvan Charles KIEGAIN DJOKO - L3
%                   Aicha BENNAGHMOUCH -L3


data(1, 3, [2,1,1,1,1,1]).
data(2, 19, [10,9,7,6,4,4,3,3,3,3,3,2,2,2,1,1,1,1,1,1]).
data(3, 112, [50,42,37,35,33,29,27,25,24,19,18,17,16,15,11,9,8,7,6,4,2]).
data(4, 175, [81,64,56,55,51,43,39,38,35,33,31,30,29,20,18,16,14,9,8,5,4,3,2,1]).

printall([], [], [], _).
printall([X|Xs], [Y|Ys], [T|Ts], S):-
	XT is X+T,
	YT is Y+T,
	format(S, "%d %d\n%d %d\n%d %d\n%d %d\n%d %d\n\n", [X,Y,XT,Y,XT,YT,X,YT,X,Y]),
        printall(Xs, Ys, Ts, S).

printsol(Sink, Xs, Ys, Ts):-
	open(Sink, write, S),
	printall(Xs, Ys, Ts, S),
	close(S).

indomain(X):-
        non_fd_var(X), !.
indomain(X):-
        fd_min(X, MinX),
        (X #= MinX; (g_inc(bt), X #\= MinX, indomain(X))).

assign(X):-
        non_fd_var(X), !.
assign(X):-
        fd_min(X, MinX),
        (X #= MinX; (g_inc(bt), X #\= MinX)).

labeling1([], _, _):- !.
labeling1(Vars, Goal, Criterion):-
        skipcst(Vars, Unks),
        Unks = [_|_] ->
        (mincrit(Unks, Criterion, Best, Rest),
	G =.. [Goal, Best],
	call(G),
        labeling1([Best|Rest], Goal, Criterion));
        true.

labeling(Xs, Ys, Goal, Criterion, B, NbSol):-
	g_assign(bt, 0),
	g_assign(nbsol, 0),
	labeling1(Xs, Goal, Criterion),
	labeling1(Ys, Goal, Criterion),
	g_inc(nbsol, NbSol),
	g_read(bt, B).

skipcst([], []).
skipcst([X|Xs], Vars):-
	non_fd_var(X), !,
	skipcst(Xs, Vars).
skipcst([X|Xs], [X|Vs]):-
	skipcst(Xs, Vs).

mincritrec([], _, _, Best, Rest, Best, Rest).
mincritrec([X|Xs], Criterion, BC, BX, Rest, B, R):-
        non_fd_var(X), !,
        mincritrec(Xs, Criterion, BC, BX, Rest, B, R).
mincritrec([X|Xs], Criterion, BC, BX, Rest, B, R):-
        GC =.. [Criterion,X,C],
        call(GC),
        C @< BC -> mincritrec(Xs, Criterion, C, X, [BX|Rest], B, R);
        mincritrec(Xs, Criterion, BC, BX, [X|Rest], B, R).


mincrit([X|Xs], Criterion, Best, Rest):-
	GC =.. [Criterion,X,C],
	call(GC),
        mincritrec(Xs, Criterion, C, X, [], Best, Rest).

minsizemin(V, [S, M]):-
        fd_size(V, S),
        fd_min(V, M).

minmin(V, M):-
        fd_min(V, M).

%-------------------------------------------------------------------------------------------------------

domain([], _, []). %prédicat pour restreindre le domaine des variables de décisions
domain([C|Cs], MAXSIZE, [T|Ts]) :-
    Max is MAXSIZE - T,
    fd_domain(C, 0, Max),
    domain(Cs, MAXSIZE, Ts).

nocover([],[],[]). %prédicat pour interdire que les petis carrés se recouvrent entre eux
nocover([X|Xs],[Y|Ys],[T|Ts]):-    
        nocoverpair(X,Y,T,Xs,Ys,Ts),
        nocover(Xs,Ys,Ts).

nocoverpair(_,_,_,[],[],[]).  %prédicat pour interdire que deux petis carrés se recouvrent entre eux
nocoverpair(X1,Y1,T1,[X2|Xs],[Y2|Ys],[T2|Ts]) :- 
        (Y1 + T1 #=< Y2)
        #\/ (Y2 + T2 #=< Y1)
        #\/ (X1 + T1 #=< X2)
        #\/ (X2 + T2 #=< X1),
        nocoverpair(X1,Y1,T1,Xs,Ys,Ts).



solve1(Num, Xs, Ys, B):- 
        data(Num, T, Ts),
        domain(Xs, T, Ts),
        domain(Ys, T, Ts),
        nocover(Xs,Ys,Ts),
        fd_labeling(Xs, [backtracks(B)]),
        fd_labeling(Ys, [backtracks(B)]),
        printsol('solution01.txt', Xs, Ys, Ts).

numlist(L, U, Ns) :- % prédicat pour générer dans Ns tous les nombres allant de U à L
        L =< U,
        numlistrec(L, U, Ns).
            
numlistrec(U, U, [U]) :- !.
numlistrec(L, U, [L|Ns]) :-
        L1 is L + 1,
        numlistrec(L1, U, Ns).
            
sumList([], 0). 
sumList([H | Q], R) :- % prédicat pour générer la somme des éléments d'une liste 
        sumList(Q, W),
        R #= H + W.

redundant_constraint_unity(_, [] , [], []).
redundant_constraint_unity(V, [H | Hx] , [T | Tx], [S | Sx]) :-
        C #<=> (H #=< V #/\ V #< H + T),
        S #= T * C,
        redundant_constraint_unity(V, Hx , Tx, Sx).

redundant_constraint([], List, Ts, T).
redundant_constraint([Vi | Q], List, Ts, T) :-
    redundant_constraint_unity(Vi, List, Ts, S),
    sumList(S, Resultat),
    T #= Resultat,    
    redundant_constraint(Q, List, Ts, T).

solve2(Num, Xs, Ys, B):- 
        data(Num, T, Ts),
        domain(Xs, T, Ts),
        domain(Ys, T, Ts),
        M is T - 1,
        numlist(0,M,V),
        redundant_constraint(V, Xs, Ts, T),
	redundant_constraint(V, Ys, Ts, T),
        nocover(Xs,Ys,Ts),
        fd_labeling(Xs, [backtracks(B)]),
        fd_labeling(Ys, [backtracks(B)]),
        printsol('solution02.txt', Xs, Ys, Ts).


/*
   Nombres de backtracks pour l'instance 1 :
   Sans contraintes : B = 2;
   Avec Contraintes : B = 0;
   on constate donc que les contraintes redondantes améliore l'efficacité en réduisant le nombre de backtrack nécessaire .
*/

solve3(Num, Xs, Ys, Goal, B, NbSol):- 
        data(Num, T, Ts),
        domain(Xs, T, Ts),
        domain(Ys, T, Ts),
        M is T - 1,
        numlist(0,M,V),
        redundant_constraint(V, Xs, Ts, T),
	redundant_constraint(V, Ys, Ts, T),
        nocover(Xs,Ys,Ts),
        labeling(Xs, Ys, Goal, minmin, B, NbSol),
        printsol('solution03.txt', Xs, Ys, Ts).

/*
   Nombres de backtracks pour l'instance 2 :
   Avec assign : B = 805 , NbSol = 1;
   Avec indomain : B = 9038, NbSol = 1;
   on constate donc que le but assign comme prévu est bien meilleure que indomain au vu de la différence entre le nombre de backtrack.
*/

sort([_], [_], [_]).
sort([X,Xi|Xs], [Y,Yi|Ys], [T,Ti|Ts]) :-
    (Ti #\= T) 
    #\/ (
        (       Yi #< Y
            #\/ Xi #< X)
        #/\ Xi #=< X),
    sort([Xi|Xs], [Yi|Ys], [Ti|Ts]).

solve4_1(Num, Xs, Ys, Goal, B, NbSol):- 
        data(Num, T, Ts),
        domain(Xs, T, Ts),
        domain(Ys, T, Ts),
        M is T - 1,
        numlist(0,M,V),
        nocover(Xs,Ys,Ts),
        redundant_constraint(V, Xs, Ts, T),
	redundant_constraint(V, Ys, Ts, T),
        sort(Xs, Ys, Ts),
        labeling(Xs, Ys, Goal, minmin, B, NbSol),
        printsol('solution04_1.txt', Xs, Ys, Ts).

/*     Nombres de backtracks pour l'instance 1 avec assign et:
        sans ordre: B = 479, NbSol = 480;
        avec ordre : B = 8, NbSol = 4;
*/

center_position_largest_square([], [], [], _).
center_position_largest_square(S,[X|Xs], [Y|Ys], [T|Ts]) :-
    S_2 is S//2,
    L_2 is T//2,
    ( X + L_2 #=< S_2 #/\ Y + L_2 #=< S_2).

solve4_2(Num, Xs, Ys, Goal, B, NbSol):- 
        data(Num, T, Ts),
        domain(Xs, T, Ts),
        domain(Ys, T, Ts),
        center_position_largest_square(T,Xs,Ys,Ts),
        M is T - 1,
        numlist(0,M,V),
        nocover(Xs,Ys,Ts),
        redundant_constraint(V, Xs, Ts, T),
        redundant_constraint(V, Ys, Ts, T),
        sort(Xs, Ys, Ts),
        labeling(Xs, Ys, Goal, minmin, B, NbSol),
        printsol('solution04_2.txt', Xs, Ys, Ts).

/*     Nombres de backtracks pour l'instance 1 avec assign et:
        sans ordre: B = 479, NbSol = 480;
        avec ordre : B = 8, NbSol = 4;
        avec ordre et restriction sur centre : B = 2, NbSol = 1 ;
        pour le cas précédent avec l'instance 2 on a : B = 8554, NbSol = 2554 ;

        
*/