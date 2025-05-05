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

 


(* TODO: finish this *)
Definition IG_to_RG {X Y : Type} (ig : IG X Y) : RG X.
Proof.
    Print labNodes.
    (* list of node labels *)
    pose (nodes := map snd (labNodes ig)).
    (* list of connections made by edges (drop labels)*)
    pose (edges := map (fun (edge : LEdge Y) => match edge with | (from, to, lab) => (lookup from ig, lookup to ig) end) (labEdges ig)).
    
    refine {|
        gr_nodes := fun (A : X) =>
                            fold_right (fun (v : X) (acc: Prop) => (A = v) \/ acc) False nodes;

        gr_edges := fun (A B : X) =>
                            fold_right (fun (e : (option X) * (option X)) (acc: Prop) => match e with
                                | (Some from, Some to) => ((A = from) /\ (B = to)) \/ acc
                                (* This case should never happen *)
                                | _ => acc
                                end) False edges;
                     
        gr_valid := _
    |}.
    unfold valid_cond. intros. split.
    - induction edges.
        + simpl in H. destruct H.
        + simpl in H. 

Admitted.
(* Defined. *)




Coercion IG_to_RG : IG >-> RG.

Definition equiv_IG {X : Type} (ig1 ig2 : IG X unit) : Prop :=
equiv_G ig1 ig2.

Notation "g1 I== g2" := (equiv_IG g1 g2) (at level 80).


(* Section to make rewrite work with equiv_IG *)

(* Source for rewrite: https://stackoverflow.com/questions/56099646/use-rewrite-tactic-with-my-own-operator-in-coq *)
Require Import Setoid Morphisms.

(* This proof is based on === being an equivalence relation *)
Instance IG_Equivalence_eq {X : Type} : Equivalence (@equiv_IG X).
Proof.
    pose proof (@RG_Equivalence_eq X). destruct H. split.
    - unfold Reflexive. intros. unfold Reflexive in Equivalence_Reflexive. apply Equivalence_Reflexive.
    - unfold Symmetric. intros. unfold Symmetric in Equivalence_Symmetric. apply Equivalence_Symmetric. apply H.
    - unfold Transitive. intros. unfold Transitive in Equivalence_Transitive. apply (Equivalence_Transitive x y z).
        + apply H.
        + apply H0.
Qed. 




(* TODO: this is hard. Check if there are any theorems on the map interface, that I can use *)
Example basic_equivalence_test : (mkGraph [(1, "1"); (2, "2")] []) I== (mkGraph [(2, "2"); (1, "1")] []).
Proof.
    unfold equiv_IG. unfold equiv_G. simpl. split; split; intros.
    - admit.
    - admit.
    - admit.
    - admit.
Qed.

