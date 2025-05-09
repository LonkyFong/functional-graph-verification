Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Sets.Ensembles.

Require Import MyProject.project.relational_graph.

(* Stated and proves Lemmas and Theorems about RGs *)

(* "RG_equiv" is an equivalence relation: *)
(* Reflexive *)
Theorem RG_equiv_Reflexive {A : Type}: forall (rg : RG A), RG_equiv rg rg.
Proof.
    firstorder.
Qed.
    

(* Symmetric *)
Theorem RG_equiv_Symmetric {A : Type}: forall (rg1 rg2 : RG A), RG_equiv rg1 rg2 <-> RG_equiv rg2 rg1.
Proof.
    firstorder.
Qed. 

(* Transitive *)
Theorem RG_equiv_Transitive {A : Type}: forall (rg1 rg2 rg3 : RG A), RG_equiv rg1 rg2 -> RG_equiv rg2 rg3 -> RG_equiv rg1 rg3.
Proof.
    firstorder.
    - apply H1. apply H2. apply H3.
    - apply H2. apply H1. apply H3.
Qed.

(* Section to make rewrite work with equiv_RG *)

(* Source for rewrite: https://stackoverflow.com/questions/56099646/use-rewrite-tactic-with-my-own-operator-in-coq *)
Require Import Setoid Morphisms.
Instance RG_Equivalence_eq {A : Type} : Equivalence (@RG_equiv A).
Proof.
    unfold RG_equiv. split.
    - unfold Reflexive. intros. pose proof (@RG_equiv_Reflexive A). apply H.
    - unfold Symmetric. intros. pose proof (@RG_equiv_Symmetric A). apply H0. apply H.
    - unfold Transitive. intros. pose proof (@RG_equiv_Transitive A). apply (H1 x y).
        + apply H.
        + apply H0.
Qed.