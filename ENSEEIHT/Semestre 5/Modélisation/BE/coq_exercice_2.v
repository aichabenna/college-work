Require Import Naturelle.
Section Session1_2021_Logique_Exercice_2.

Variable A B C : Prop.

Theorem Exercice_2_Naturelle : ((A /\ B) -> C) -> ((A -> C) \/ (B -> C)).
Proof.
I_imp H1.
E_ou A (~A).
TE.
I_imp H2.
I_ou_d.
I_imp H3.
E_imp (A /\ B).
Hyp H1.
I_et.
Hyp H2.
Hyp H3.
I_imp H4.
I_ou_g.
I_imp H5.
E_antiT.
E_non A.
Hyp H5.
Hyp H4.
Qed.

Theorem Exercice_2_Coq : ((A /\ B) -> C) -> ((A -> C) \/ (B -> C)).
Proof.
intros.
right.
intro H1.
cut (A /\ B).
exact H.
split.
cut (A \/ ~A).
intro Hgng.
elim Hgng.
intro Hg.
exact Hg.
intro H2.
cut (A /\ B).
intro H3.
elim H3.
intros HA HB.
exact HA.
split.

cut False.
intro H2.
contradiction.
absurd A.
elim Hgng.
intro H3.
intro H4.

apply (classic A).
Qed.

End Session1_2021_Logique_Exercice_2.

