(* Les règles de la déduction naturelle doivent être ajoutées à Coq. *) 
Require Import Naturelle. 

(* Ouverture d'une section *) 
Section LogiqueProposition. 

(* Déclaration de variables propositionnelles *) 
Variable A B C E Y R : Prop. 

Theorem Thm_0 : A /\ B -> B /\ A.
Proof.
I_imp HAetB.
I_et.
E_et_d A.
Hyp HAetB.
E_et_g B.
Hyp HAetB.
Qed.

Theorem Thm_1 : ((A \/ B) -> C) -> (B -> C).
Proof.
I_imp H1.
I_imp H2.
E_imp (A \/ B).
Hyp H1.
I_ou_d.
Hyp H2.
Qed.

Theorem Thm_2 : A -> ~~A.
Proof.
I_imp HA.
I_non H1.
E_non A.
Hyp HA.
Hyp H1. 
Qed.

Theorem Thm_3 : (A -> B) -> (~B -> ~A).
I_imp H1.
I_imp H2.
I_non HA.
E_non B.
E_imp A.
Hyp H1.
Hyp HA.
Hyp H2.
Qed.

Theorem Thm_4 : (~~A) -> A.
I_imp H1.
absurde H.
I_antiT (~A).
Hyp H.
Hyp H1.
Qed.

Theorem Thm_5 : (~B -> ~A) -> (A -> B).
I_imp H1.
I_imp H2.
absurde H.
I_antiT A.
Hyp H2.
E_imp (~B).
Hyp H1.
Hyp H.
Qed.

Theorem Thm_6 : ((E -> (Y \/ R)) /\ (Y -> R)) -> ~R -> ~E.
I_imp H1.
I_imp H2.
I_non HE.
I_antiT R.
E_imp Y.
E_et_d (E -> Y \/ R).
Hyp H1.
E_ou Y R.
E_imp E.
E_et_g (Y->R).
Hyp H1.
Hyp HE.
I_imp HY.
Hyp HY.
I_imp HR.
E_antiT.
E_non R.
Hyp HR.
Hyp H2.
Hyp H2.
Qed.

(* Version en Coq *)

Theorem Coq_Thm_0 : A /\ B -> B /\ A.
intro H.
destruct H as (HA,HB).  (* élimination conjonction *)
split.                  (* introduction conjonction *)
exact HB.               (* hypothèse *)
exact HA.               (* hypothèse *)
Qed.

Theorem Coq_E_imp : ((A -> B) /\ A) -> B.
intro H.
destruct H as (H1,H2).
cut A.
exact H1.
exact H2.
Qed.

Theorem Coq_E_et_g : (A /\ B) -> A.
intro H.
destruct H as (H1,H2).
exact H1.
Qed.

Theorem Coq_E_ou : ((A \/ B) /\ (A -> C) /\ (B -> C)) -> C.
intro H.
destruct H as (H1,H2).
destruct H2 as (H2,H3).
destruct H1 as [H4|H5].
cut A.
exact (H2).
exact (H4).
cut B.
exact (H3).
exact(H5).
Qed.

Theorem Coq_Thm_7 : ((E -> (Y \/ R)) /\ (Y -> R)) -> (~R -> ~E).
intro H1.
destruct H1 as (H11,H12).
intro H2.
intro H3.
absurd R.
exact H2.
cut Y.
exact H12.
destruct H11.
exact H3.
exact H.

cut False.
intro H4.
contradiction.
absurd R.
exact H2.
exact H.

Qed.


End LogiqueProposition.

