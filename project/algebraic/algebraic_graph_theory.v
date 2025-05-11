Require Import Setoid Morphisms.

Require Import MyProject.project.algebraic.algebraic_graph.
Require Import MyProject.project.algebraic.algebraic_graph_to_RG.

Require Import MyProject.project.relational_graph.
(* Notice how this file "does"  need relational_graph_theory  *)
Require Import MyProject.project.relational_graph_theory.




Ltac AG_axiom_proof_automation_via_RG H H0 :=
    unfold AG_equiv; intros; split; split; intros; simpl; simpl in H; repeat (destruct H || destruct H0); auto
.

(* These are the "8 axioms" originally proposed by  functional graphs with class *)

(* +++ is commutative and associative *)
Theorem AG_Overlay_Commutative {A : Type} : forall (ag1 ag2 : AG A), ag1 +++ ag2 A== ag2 +++ ag1.
Proof.
        AG_axiom_proof_automation_via_RG H H0.
Qed.

Theorem AG_Overlay_Associative {A : Type} : forall (ag1 ag2 ag3 : AG A), ag1 +++ (ag2 +++ ag3) A== (ag1 +++ ag2) +++ ag3.
Proof.
    AG_axiom_proof_automation_via_RG H H0.
Qed.

(* (G, ***, e) is a monoid *)
Theorem AG_Empty_Connect_L_Identity {A : Type} : forall (ag : AG A), Empty *** ag A== ag.
Proof.
    AG_axiom_proof_automation_via_RG H H0.
Qed.

Theorem AG_Empty_Connect_R_Identity {A : Type} : forall (ag : AG A), ag *** Empty A== ag.
Proof.
    AG_axiom_proof_automation_via_RG H H0.
Qed.

Theorem AG_Connect_Associative {A : Type} : forall (ag1 ag2 ag3 : AG A), ag1 *** (ag2 *** ag3) A== (ag1 *** ag2) *** ag3.
Proof.
    AG_axiom_proof_automation_via_RG H H0.
Qed.

(* *** distributes over +++ *)
Theorem AG_Connect_Overlay_L_Distributes {A : Type} : forall (ag1 ag2 ag3 : AG A), ag1 *** (ag2 +++ ag3) A== ag1 *** ag2 +++ ag1 *** ag3.
Proof.
    AG_axiom_proof_automation_via_RG H H0.
Qed.

Theorem AG_Connect_Overlay_R_Distributes {A : Type} : forall (ag1 ag2 ag3 : AG A), (ag1 +++ ag2) *** ag3 A== ag1 *** ag3 +++ ag2 *** ag3.
Proof.
    AG_axiom_proof_automation_via_RG H H0.
Qed.

(* Decomposition *)
Theorem AG_Connect_Decomposition {A : Type} : forall (ag1 ag2 ag3 : AG A), ag1 *** ag2 *** ag3 A== ag1 *** ag2 +++ ag1 *** ag3 +++ ag2 *** ag3.
Proof.
    AG_axiom_proof_automation_via_RG H H0.
Qed.



(* Show that AG_to_RG is are "complete" and "sound"  *)
(* TODO: this is not very urgent right now, but is possibly necessary for model-based specification *)

(* Complete: *)
(* Look at paper *)

(* Sound: *)



(* Section to make rewrite work with equiv_AG *)
(* This proof is based on === being an equivalence relation *)
Instance AG_Equivalence_eq {A : Type} : Equivalence (@AG_equiv A).
Proof.
    G_derived_equivalence_prover A unit (@AG_to_RG_unlE A).
Qed.
         

Ltac Proper_proof_automation H1 := split; split; intros; simpl in *; destruct H1; firstorder.


Instance Proper_add {A : Type} : Proper ((@AG_equiv A) ==> AG_equiv ==> AG_equiv) Overlay.
Proof.
    Proper_proof_automation H1.
Qed.


Instance Proper_mul {A : Type} : Proper ((@AG_equiv A) ==> AG_equiv ==> AG_equiv) Connect.
Proof.
    Proper_proof_automation H1.
Qed.




(* Theorems that can be made based on the "8 axioms": 
They can all be proven using "AG_axiom_proof_automation_via_RG", but I should find a way to do it using the axioms *)
(* These proofs are heavily inspired by: http://async.org.uk/tech-reports/NCL-EEE-MICRO-TR-2014-191.pdf *)


(* This is a helper for Identity of + *)
Lemma rdeco {A : Type}: forall (ag : AG A), ag +++ ag +++ Empty A== ag.
Proof.
    intros.
    pose proof (AG_Connect_Decomposition ag Empty Empty).

    rewrite AG_Empty_Connect_R_Identity in H.
    rewrite AG_Empty_Connect_R_Identity in H.
    rewrite <- H.

    reflexivity.
Qed.


(* Identity of + *)
Theorem AG_Empty_Overlay_R_Identity {A : Type}: forall (g : AG A), g +++ Empty A== g.
Proof.
    intros.
    rewrite <- rdeco.

    rewrite <- AG_Overlay_Associative.
    rewrite (AG_Overlay_Associative Empty (g +++ Empty)). 
    rewrite (AG_Overlay_Commutative Empty (g +++ Empty)).
    rewrite <- AG_Overlay_Associative.
    rewrite <- AG_Overlay_Associative.

    rewrite (rdeco).
    rewrite (rdeco).
    reflexivity.
Qed.


(* idempotence of + *)
Theorem AG_Overlay_Idempotence {A : Type}: forall (ag : AG A), ag +++ ag A== ag.
Proof.
    intros.
    pose proof rdeco ag.
    rewrite AG_Empty_Overlay_R_Identity in H.
    auto.
Qed.



(* Absorption (proof is mine) *)
Theorem AG_Absorption {A : Type}: forall (ag1 ag2 : AG A), ag1 *** ag2 +++ ag1 +++ ag2 A== ag1 *** ag2.
Proof.
    intros. pose proof AG_Connect_Decomposition ag1 ag2 Empty.
    rewrite (AG_Connect_Associative) in H.
    rewrite AG_Empty_Connect_R_Identity in H.
    rewrite AG_Empty_Connect_R_Identity in H.
    rewrite AG_Empty_Connect_R_Identity in H.
    symmetry in H.
    auto.
Qed.


(* Saturation (proof is mine) *)
Theorem AG_Saturation {A : Type}: forall (ag : AG A), ag *** ag *** ag A== ag *** ag.
Proof.
    intros.
    rewrite AG_Connect_Decomposition.

    rewrite AG_Overlay_Idempotence.
    rewrite AG_Overlay_Idempotence.
    reflexivity.
Qed.

