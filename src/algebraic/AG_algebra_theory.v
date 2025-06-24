Require Import Setoid Morphisms.
Require Import Ensembles.

Require Import List.
Import ListNotations.
Require Import Sorting.Permutation.

Require Import GraphVerification.src.util.NatSet.

Require Import GraphVerification.src.relational.RG.
Require Import GraphVerification.src.relational.RG_theory.

Require Import GraphVerification.src.algebraic.AG.
Require Import GraphVerification.src.algebraic.AG_to_RG.

(** Stating and proving Lemmas and THeorems about the algebraic properties of AGs 
    A noteworthy result is that we show that
    the definition-based interpretation of an AG is equivalent to the algebraic interpretation *)


(** This is used to verify that the axioms on the algebra of AGs are consistent
    with the interpretation of the expressions in terms of RGs *)
Ltac AG_axiom_proof_automation_via_RG :=
    unfold AG_equiv; simpl; firstorder.

(* These are the "8 axioms" as presented in "Algebraic graphs with class (functional pearl)" by Mokhov *)

(* +++ is commutative and associative *)
Theorem AG_overlay_Commutative {A : Type} : forall (ag1 ag2 : AG A), ag1 +++ ag2 ==A ag2 +++ ag1.
Proof.
    AG_axiom_proof_automation_via_RG.
Qed.

Theorem AG_overlay_Associative {A : Type} : forall (ag1 ag2 ag3 : AG A), ag1 +++ (ag2 +++ ag3) ==A (ag1 +++ ag2) +++ ag3.
Proof.
    AG_axiom_proof_automation_via_RG.
Qed.

(* (G, ***, e) is a monoid *)
Theorem AG_empty_connect_L_Identity {A : Type} : forall (ag : AG A),
    AG_empty *** ag ==A ag.
Proof.
    AG_axiom_proof_automation_via_RG.
Qed.

Theorem AG_empty_connect_R_Identity {A : Type} : forall (ag : AG A),
    ag *** AG_empty ==A ag.
Proof.
    AG_axiom_proof_automation_via_RG.
Qed.

Theorem AG_connect_Associative {A : Type} : forall (ag1 ag2 ag3 : AG A),
    ag1 *** (ag2 *** ag3) ==A (ag1 *** ag2) *** ag3.
Proof.
    AG_axiom_proof_automation_via_RG.
Qed.

(* *** distributes over +++ *)
Theorem AG_connect_overlay_L_Distributes {A : Type} : forall (ag1 ag2 ag3 : AG A),
    ag1 *** (ag2 +++ ag3) ==A ag1 *** ag2 +++ ag1 *** ag3.
Proof.
    AG_axiom_proof_automation_via_RG.
Qed.

Theorem AG_connect_overlay_R_Distributes {A : Type} : forall (ag1 ag2 ag3 : AG A),
    (ag1 +++ ag2) *** ag3 ==A ag1 *** ag3 +++ ag2 *** ag3.
Proof.
    AG_axiom_proof_automation_via_RG.
Qed.

(* Decomposition *)
Theorem AG_connect_Decomposition {A : Type} : forall (ag1 ag2 ag3 : AG A),
    ag1 *** ag2 *** ag3 ==A ag1 *** ag2 +++ ag1 *** ag3 +++ ag2 *** ag3.
Proof.
    AG_axiom_proof_automation_via_RG.
Qed.




(** Section to make rewrite work with ==A of overlays and connects *)

(* This proof is based on ==R being an equivalence relation *)
Instance AG_Equivalence {A : Type} : Equivalence (@AG_equiv A).
Proof.
    G_derived_equivalence_prover A unit (@AG_to_RG A).
Qed.

Ltac Proper_proof_automation := split; simpl in *; firstorder.

Instance Proper_overlay {A : Type} : Proper ((@AG_equiv A) ==> AG_equiv ==> AG_equiv) AG_overlay.
Proof.
    Proper_proof_automation.
Qed.

Instance Proper_connect {A : Type} : Proper ((@AG_equiv A) ==> AG_equiv ==> AG_equiv) AG_connect.
Proof.
    Proper_proof_automation.
Qed.



(** The following theorems are provable using the same automation as the 8 axioms,
    but this section aims to demonstrate their utility, by using only them.
    This has already been done in the Agda formalization by Andrey Mokhov *)

(* This is a helper for multiple theorems *)
Lemma _overlay_preidempotence {A : Type}: forall (ag : AG A), ag +++ ag +++ AG_empty ==A ag.
Proof.
    intros.
    pose proof (AG_connect_Decomposition ag AG_empty AG_empty).

    rewrite AG_empty_connect_R_Identity in H.
    rewrite AG_empty_connect_R_Identity in H.
    rewrite <- H.

    reflexivity.
Qed.


(* Identity of + *)
Theorem AG_empty_overlay_R_Identity {A : Type}: forall (g : AG A), g +++ AG_empty ==A g.
Proof.
    intros.
    rewrite <- _overlay_preidempotence.

    rewrite <- AG_overlay_Associative.
    rewrite (AG_overlay_Associative AG_empty (g +++ AG_empty)). 
    rewrite (AG_overlay_Commutative AG_empty (g +++ AG_empty)).
    rewrite <- AG_overlay_Associative.
    rewrite <- AG_overlay_Associative.

    rewrite _overlay_preidempotence.
    rewrite _overlay_preidempotence.
    reflexivity.
Qed.


(* Idempotence of + *)
Theorem AG_overlay_Idempotence {A : Type}: forall (ag : AG A), ag +++ ag ==A ag.
Proof.
    intros.
    pose proof _overlay_preidempotence ag.
    rewrite AG_empty_overlay_R_Identity in H.
    assumption.
Qed.


(* Absorption *)
Theorem AG_Absorption {A : Type}: forall (ag1 ag2 : AG A), ag1 *** ag2 +++ ag1 +++ ag2 ==A ag1 *** ag2.
Proof.
    intros. pose proof AG_connect_Decomposition ag1 ag2 AG_empty.
    rewrite (AG_connect_Associative) in H.
    rewrite AG_empty_connect_R_Identity in H.
    rewrite AG_empty_connect_R_Identity in H.
    rewrite AG_empty_connect_R_Identity in H.
    symmetry in H.
    assumption.
Qed.


(* Saturation *)
Theorem AG_Saturation {A : Type}: forall (ag : AG A), ag *** ag *** ag ==A ag *** ag.
Proof.
    intros.
    rewrite AG_connect_Decomposition.

    rewrite AG_overlay_Idempotence.
    rewrite AG_overlay_Idempotence.
    reflexivity.
Qed.
