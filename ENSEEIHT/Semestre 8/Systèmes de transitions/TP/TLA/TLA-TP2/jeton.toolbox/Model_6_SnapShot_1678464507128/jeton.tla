---------------- MODULE jeton ----------------
\* Time-stamp: <07 mar 2013 15:49 queinnec@enseeiht.fr>

(* Algorithme d'exclusion mutuelle à base de jeton. *)

EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME N \in Nat /\ N > 1

Processus == 0..N-1

Hungry == "H"
Thinking == "T"
Eating == "E"

VARIABLES
  etat,
  jeton

TypeInvariant ==
   [] (/\ etat \in [ Processus -> {Hungry,Thinking,Eating} ]
       /\ jeton \in [ Processus -> BOOLEAN ])

ExclMutuelle == [] (\A i,j \in Processus : jeton[i] /\ jeton[j] => i = j)

VivaciteIndividuelle == \A i \in Processus: etat[i] = Hungry ~> etat[i] = Eating

VivaciteGlobale == \E i \in Processus: etat[i] = Hungry ~> \E j \in Processus: etat[j] = Eating

JetonVaPartout == \A i \in Processus: TRUE ~> jeton[i]

Sanity ==
  [] (\A i \in Processus : etat[i] = Eating => jeton[i] = TRUE)

----------------------------------------------------------------

Init ==
 /\ etat = [ i \in Processus |-> Thinking ]
 /\ jeton = [ i \in Processus |-> i = 0 ]

demander(i) ==
  /\ etat[i] = Thinking
  /\ etat' = [ etat EXCEPT ![i] = Hungry ]
  /\ UNCHANGED jeton

entrer(i) ==
  /\ etat[i] = Hungry
  /\ jeton[i]
  /\ etat' = [ etat EXCEPT ![i] = Eating ]
  /\ UNCHANGED jeton

sortir(i) ==
  /\ etat[i] = Eating
  /\ etat' = [ etat EXCEPT ![i] = Thinking ]
  /\ UNCHANGED jeton

bouger(i) ==
  /\ jeton[i] 
  /\ etat[i] /= Hungry
  /\ jeton' = [jeton EXCEPT ![i]=FALSE, ![(i+1)%N]=TRUE]
  /\ UNCHANGED etat

Next ==
 \E i \in Processus :
    \/ demander(i)
    \/ entrer(i)
    \/ sortir(i)
    \/ bouger(i)

Fairness == \A i \in Processus :
              /\ WF_<<etat,jeton>> (sortir(i))
              /\ WF_<<etat,jeton>> (bouger(i))
              /\ WF_<<etat,jeton>> (entrer(i))

Spec ==
 /\ Init
 /\ [] [ Next ]_<<etat,jeton>>
 /\ Fairness

================
