---------------- MODULE jeton ----------------
\* Time-stamp: <07 mar 2013 15:49 queinnec@enseeiht.fr>

(* Algorithme d'exclusion mutuelle à base de jeton. *)

EXTENDS Naturals, FiniteSets, Sequences

CONSTANT N

ASSUME N \in Nat /\ N > 1

Processus == 0..N-1

Hungry == "H"
Thinking == "T"
Eating == "E"

VARIABLES
  etat,
  jeton,
  canal

TypeInvariant ==
   [] (/\ etat \in [ Processus -> {Hungry,Thinking,Eating} ]
       /\ jeton \in [ Processus -> BOOLEAN ]
       /\ canal \in [ Processus -> Seq(BOOLEAN) ])

ExclMutuelle == [] (\A i,j \in Processus : (jeton[i] /\ jeton[j] => i = j) /\ (canal[i]= <<TRUE>> /\ canal[j]= <<TRUE>> => i = j) /\ (jeton[i] => canal[j] = <<>>) /\ (canal[j] = <<TRUE>> => jeton[i] = FALSE))

VivaciteIndividuelle == \A i \in Processus: etat[i] = Hungry ~> etat[i] = Eating

VivaciteGlobale == \E i \in Processus: etat[i] = Hungry ~> \E j \in Processus: etat[j] = Eating

JetonVaPartout == \A i \in Processus: (TRUE ~> jeton[i]) /\ (TRUE ~> canal[i] = <<TRUE>>)

Sanity ==
  [] (\A i \in Processus : etat[i] = Eating => jeton[i] = TRUE)

----------------------------------------------------------------

Init ==
 /\ etat = [ i \in Processus |-> Thinking ]
 /\ jeton = [ i \in Processus |-> i = 0 ]
 /\ canal = [ i \in Processus |-> <<>> ]

demander(i) ==
  /\ etat[i] = Thinking
  /\ etat' = [ etat EXCEPT ![i] = Hungry ]
  /\ UNCHANGED jeton
  /\ UNCHANGED canal

entrer(i) ==
  /\ etat[i] = Hungry
  /\ jeton[i]
  /\ etat' = [ etat EXCEPT ![i] = Eating ]
  /\ UNCHANGED jeton
  /\ UNCHANGED canal

sortir(i) ==
  /\ etat[i] = Eating
  /\ jeton[i]
  /\ jeton' = [jeton EXCEPT ![i]=FALSE]
  /\ canal' = [ canal EXCEPT ![(i+1)%N]= <<TRUE>> ]
  /\ etat' = [ etat EXCEPT ![i] = Thinking ]

bouger(i) ==
  /\ jeton[i] 
  /\ etat[i] = Thinking
  /\ jeton' = [jeton EXCEPT ![i]=FALSE]
  /\ canal' = [ canal EXCEPT ![(i+1)%N]= <<TRUE>> ]
  /\ UNCHANGED etat
 
fromCanal(i) ==
    /\ canal[i] = <<TRUE>>
    /\ canal' = [ canal EXCEPT ![i]= <<>> ]
    /\ jeton' = [jeton EXCEPT ![i]=TRUE]
    /\ UNCHANGED etat
    

Next ==
 \E i \in Processus :
    \/ demander(i)
    \/ entrer(i)
    \/ sortir(i)
    \/ bouger(i)
    \/ fromCanal(i)

Fairness == \A i \in Processus :
              /\ WF_<<etat,jeton>> (sortir(i))
              /\ WF_<<etat,jeton>> (bouger(i))
              /\ WF_<<etat,jeton>> (entrer(i))

Spec ==
 /\ Init
 /\ [] [ Next ]_<<etat,jeton>>
 /\ Fairness

================
