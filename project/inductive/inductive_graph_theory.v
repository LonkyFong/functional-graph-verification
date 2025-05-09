Require Import String.
Require Import Coq.Arith.Arith.
Open Scope string_scope.

Require Import List.
Require Import Bool.
Import ListNotations.

Require Import MyProject.project.inductive.inductive_graph.
Require Import MyProject.project.relational_graph.

(* Defining Conversion from Inductive Graph to Record Graph *)


(* TODO: add some kind of well-formedness condition 
( think of the BSt invariant, which insert does not break)
 What is the correctness invariant for an inductive graph? *)

 

Definition labEdges {A B : Type} (ig : IG A B) : list (LEdge B).
Proof.
Admitted. 

(* TODO: finish this *)
Definition IG_to_RG {A B : Type} (ig : IG A B) : RG A.
Proof.
    Print labNodes.
    (* list of node labels *)
    pose (nodes := map snd (labNodes ig)).
    (* list of connections made by edges (drop labels)*)
    pose (edges := map (fun (edge : LEdge B) => match edge with | (from, to, lab) => (lookup from ig, lookup to ig) end) (labEdges ig)).
    
    refine {|
        RG_nodes := fun (a : A) =>
                            fold_right (fun (v : A) (acc: Prop) => (a = v) \/ acc) False nodes;

        RG_edges := fun (a1 a2 : A) =>
                            fold_right (fun (e : (option A) * (option A)) (acc: Prop) => match e with
                                | (Some from, Some to) => ((a1 = from) /\ (a2 = to)) \/ acc
                                (* This case should never happen *)
                                | _ => acc
                                end) False edges;
                     
        RG_valid := _
    |}.
    RG_valid_prover.
Admitted.





Coercion IG_to_RG : IG >-> RG.

Definition IG_equiv {A : Type} (ig1 ig2 : IG A unit) : Prop :=
RG_equiv ig1 ig2.

Notation "g1 I== g2" := (IG_equiv g1 g2) (at level 80).


(* Section to make rewrite work with IG_equiv *)

(* Source for rewrite: https://stackoverflow.com/questions/56099646/use-rewrite-tactic-with-my-own-operator-in-coq *)
Require Import Setoid Morphisms.

(* This proof is based on === being an equivalence relation *)
Instance IG_Equivalence_eq {A : Type} : Equivalence (@IG_equiv A).
Proof.
    pose proof (@RG_Equivalence_eq A). destruct H. split.
    - unfold Reflexive. intros. unfold Reflexive in Equivalence_Reflexive. apply Equivalence_Reflexive.
    - unfold Symmetric. intros. unfold Symmetric in Equivalence_Symmetric. apply Equivalence_Symmetric. apply H.
    - unfold Transitive. intros. unfold Transitive in Equivalence_Transitive. apply (Equivalence_Transitive x y z).
        + apply H.
        + apply H0.
Qed. 




(* TODO: this is hard. Check if there are any theorems on the map interface, that I can use *)
Example basic_equivalence_test : (mkGraph [(1, "1"); (2, "2")] []) I== (mkGraph [(2, "2"); (1, "1")] []).
Proof.
    unfold IG_equiv. unfold RG_equiv. simpl. split; split; intros.
    - admit.
    - admit.
    - admit.
    - admit.
Admitted.

