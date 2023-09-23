---------------------------- MODULE philosophes1 ----------------------------

(* Philosophes. Version en utilisant les fourchettes avec ordre et un gaucher. *)

EXTENDS Naturals

CONSTANT N

Philos == 0..N-1
Fourchettes == Philos

gauche(i) == (i+1)%N       \* philosophe à gauche du philo n°i
droite(i) == (i+N-1)%N     \* philosophe à droite du philo n°i

fg(i) == i
fd(i) == droite(i)

Gaucher == 0

Libre == N

Hungry == "H"
Thinking == "T"
Eating == "E"

VARIABLES
    etat,         \* i -> Hungry,Thinking,Eating
    etatFourchettes

TypeInvariant == [](etat \in [ Philos -> { Hungry, Thinking, Eating }] /\ etatFourchettes \in [Philos -> (0..N)])
AbsenceFamine == \A i \in Philos: etat[i] = Hungry ~> etat[i] = Eating
AbsenceBlocage == \E i \in Philos: etat[i] = Hungry ~> (\E j \in Philos: etat[j] = Eating)
Exclusion == [] (\A i \in Philos: (etat[i] = Eating) => (etat[gauche(i)] # Eating /\ etat[droite(i)] # Eating))

Dignite == [] (\A i \in Philos: etat[i] = Eating => etatFourchettes[fg(i)] = i /\ etatFourchettes[fg(i)] = i)
Respect == [] (\A i \in Philos: etat[i] = Thinking => etatFourchettes[fg(i)] # i /\ etatFourchettes[fg(i)] # i)
AbsenceVol == [] (\A i \in Philos: \A j \in Fourchettes: etatFourchettes[j] = i => (j = fg(i) \/ j = fd(i)))

----------------------------------------------------------------

Init == 
    /\ etat = [ i \in Philos |-> Thinking ]
    /\ etatFourchettes = [ i \in Fourchettes |-> Libre ]

demande(i) == 
    /\ etat[i] = Thinking
    /\ etat' = [ etat EXCEPT ![i] = Hungry ]
    /\ UNCHANGED etatFourchettes

priseG(i) ==
    /\ etat[i] = Hungry
    /\ etatFourchettes[fg(i)] = Libre
    /\ \/ i = Gaucher /\ etatFourchettes[fd(i)] = i
       \/ i # Gaucher
    /\ etatFourchettes' = [etatFourchettes EXCEPT ![fg(i)] = i]
    /\ UNCHANGED etat
    
priseD(i) ==
    /\ etatFourchettes[fd(i)] = Libre
    /\ \/ i = Gaucher
       \/ i # Gaucher /\ etatFourchettes[fg(i)] = i
    /\ etat[i] = Hungry
    /\ etatFourchettes' = [etatFourchettes EXCEPT ![fd(i)] = i]
    /\ UNCHANGED etat

mange(i) ==
    /\ etat[i] = Hungry
    /\ etatFourchettes[fd(i)] = i
    /\ etatFourchettes[fg(i)] = i
    /\ etat' = [ etat EXCEPT ![i] = Eating ]
    /\ UNCHANGED etatFourchettes

pense(i) ==
    /\ etat[i] = Eating
    /\ etat' = [ etat EXCEPT ![i] = Thinking ]
    /\ etatFourchettes' = [ etatFourchettes EXCEPT ![fg(i)] = Libre, ![fd(i)] = Libre ]

Next ==
  \E i \in Philos : \/ demande(i)
                    \/ priseG(i)
                    \/ priseD(i)
                    \/ mange(i)
                    \/ pense(i)

Fairness == \A i \in Philos:
                /\ WF_<<etat,etatFourchettes>> (mange(i))
                /\ WF_<<etat,etatFourchettes>> (pense(i))
                /\ SF_<<etat,etatFourchettes>> (priseG(i))
                /\ SF_<<etat,etatFourchettes>> (priseD(i))

Spec ==
  /\ Init
  /\ [] [ Next ]_<<etat,etatFourchettes>>
  /\ Fairness

================================