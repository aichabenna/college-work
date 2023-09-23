----------------------------- MODULE cannibales -----------------------------


=============================================================================
\* Modification History
\* Last modified Fri Feb 17 12:02:26 CET 2023 by ahamoir
\* Created Fri Feb 17 10:33:38 CET 2023 by ahamoir

DEFINE
    Cardinality,
    Nat

CONSTANT
    nbMissionaires,
    nbCannibales,
    tailleBarque

VARIABLES
    cannibales,
    missionaires,
    barque
    
Rives == {"G", "D"}
inv(r) == IF r = "G" THEN "D" ELSE "G"

Init ==
    /\ missionaires = [x \in 1..nbMissionaires |-> "G"]
    /\ cannibales = [x \in 1..nbCannibales |-> "G"]
    /\ barque = "G"
    
TypeInvariant ==
    [] (/\ \A x \in cannibales : x \in Rives
        /\ \A x \in missionaires : x \in Rives
        /\ Cardinality(cannibales) = nbCannibales
        /\ Cardinality(missionaires) = nbMissionaires
        /\ barque \in Rives)
    
nb(ens, val) == Cardinality({x \in ens : x = val})
safe(rive) == 
    \/ nb(cannibales, rive) \leq nb(missionaires, rive)
    \/ nb(missionaires, rive) = 0
   
Safe == safe("G") /\ safe("D")

Solution == 
    [] \neg(/\ \A x \in cannibales : x = "D" 
            /\ \A x \in missionaires : x = "D")

nextEnsemble(ensemble, card, nb) ==
    [x \in 1..card |->
        IF x \in (CHOOSE ens : 
                    /\ \A elt \in ens :
                        /\ elt \in 1..card
                        /\ Cardinality({elt2 \in ens : elt2 = elt}) = 1
                        /\ ensemble[elt] = rive
                    /\ Cardinality(ens) = nb)
        THEN inv(rive)
        ELSE ensemble[x]] 

\* Déplacer "a" cannibales et "b" missionaires depuis la rive "rive"
Deplacer(rive, a, b) ==
    /\ barque = rive
    /\ a + b \leq tailleBarque
    /\ a + b \geq 1
    /\ nb(cannibales, rive) \geq a
    /\ nb(missionaires, rive) \geq b
    /\ cannibales' = nextEnsemble(cannibale, nbCannibales, a)
    /\ missionaires' = nextEnsemble(missionaire, nbMissionaires, b)

Next == \E <<rive, a, b>> \in Rives \X Nat \X Nat : Deplacer(rive, a, b)

Spec == Init /\ [] [ Next ]_<<cannibales, missionaires, barque>>
    
    