Require Import String.
Require Import Coq.Arith.Arith.
Open Scope string_scope.

Require Import List.
Require Import Bool.
Import ListNotations.

Require Import GraphVerification.src.util.util.

(* Require Import GraphVerification.src.relational_graph.
 *)

Require Import Coq.Sets.Ensembles.
Require Import Setoid Morphisms.


Require Import GraphVerification.src.util.NatSet.
Require Import GraphVerification.src.relational_graph.
Require Import GraphVerification.src.relational_graph_theory.
Require Import GraphVerification.src.relational_graph_IG_operations.


Open Scope nat_scope.

(* Specifies behavior of IH functions on an (edge-label compatible) RG via equational specification *)


(* Proving also Adj and Context equivalence relations *)

Instance RG_Adj_Equivalence {A B : Type} : Equivalence (@RG_Adj_equiv A B).
Proof.
  unfold RG_Adj_equiv. split.
  - firstorder.
  - firstorder.
  - unfold Transitive. firstorder.
    + apply H0. apply H. assumption.
    + apply H. apply H0. assumption.
Qed.

(* Maybe its worth it to make theorem that a conjuction os equivlaence relations is also an equivalence relation *)
Instance RG_Context_Equivalence {A B : Type} : Equivalence (@RG_Context_equiv A B).
Proof.
  unfold RG_Context_equiv. pose proof (@RG_Adj_Equivalence A B). destruct H. split.
  - unfold Reflexive in *. intros. destruct x as [[froms node] tos]. firstorder.
  - unfold Symmetric in *. intros.
    destruct x as [[froms1 node1] tos1]. destruct y as [[froms2 node2] tos2].
    firstorder.
  - unfold Transitive in *.
    destruct x as [[froms1 node1] tos1]. destruct y as [[froms2 node2] tos2]. destruct z as [[froms3 node3] tos3].
    intros. destruct H as [a1 [b1 c1]]. destruct H0 as [a2 [b2 c2]]. split.
    + rewrite a1. rewrite a2. reflexivity.
    + split.
      -- rewrite b1. rewrite b2. reflexivity.
      -- rewrite c1. rewrite c2. reflexivity.
Qed.


Instance RG_Decomp_Equivalence {A B : Type} : Equivalence (@RG_Decomp_equiv A B).
Proof.
  unfold RG_Decomp_equiv. pose proof (@RG_Context_Equivalence A B). pose proof (@RG_Equivalence A B). destruct H. destruct H0. split.
  - unfold Reflexive in *. intros. destruct x as [[opt context] rg]. firstorder.
  - unfold Symmetric in *. intros.
    destruct x as [[opt1 context1] rg1]. destruct y as [[opt2 context2] rg2].
    firstorder.
  - unfold Transitive in *.
    destruct x as [[opt1 context1] rg1]. destruct y as [[opt2 context2] rg2]. destruct z as [[opt3 context3] rg3].
    firstorder.
    + apply H3. apply H7. assumption.
    + apply H7. apply H3. assumption.
Qed.


(* 5 statements on inserting (helpers for mkGraph): update, insEdge, insEdges, insNode, insNodes *)



Lemma RG_insEdge_does_not_add_node : forall (A B : Type) (edge : (RG_Edge A B)) (rg : RG A B),
  RG_labNodes (_insEdge edge rg) S== RG_labNodes rg.
Proof.
  intros.
  destruct edge as [[from to] lab]. simpl. unfold RG_labNodes. reflexivity.
Qed.



Lemma RG_insEdges_does_not_add_nodes : forall (A B : Type) (edges : list (RG_Edge A B)) (rg : RG A B),
  RG_labNodes (_insEdges edges rg) S== RG_labNodes rg.
Proof.
  intros.
  unfold _insEdges. induction edges; simpl.
  - reflexivity.
  - rewrite RG_insEdge_does_not_add_node. rewrite IHedges. reflexivity.
Qed.



(* Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

Ltac breakup_Ensemble_equality :=
  apply functional_extensionality; intros; apply propositional_extensionality; intros; split. *)

Lemma RG_insNode_any_ins_node : forall (A B : Type) (node : A) (rg : RG A B),
  RG_labNodes (_insNode node rg) S== Ensemble_add node (RG_labNodes rg).
Proof.
  firstorder.
Qed.


Lemma RG_insNodes_any_ins_all_nodes : forall (A B : Type) (nodes : list A) (rg : RG A B),
  RG_labNodes (_insNodes nodes rg) S== Ensemble_union (cListToEnsemble nodes) (RG_labNodes rg).
Proof.
  intros. induction nodes; simpl.
  - firstorder.
  - firstorder.
Qed.



Lemma RG_insEdge_on_empty_is_empty : forall (A B : Type) (edge : (RG_Edge A B)),
  _insEdge edge RG_empty R== RG_empty.
Proof.
  intros. unfold RG_equiv. destruct edge as [[from to] lab]. split.
  - firstorder.
  - firstorder.
Qed.



Lemma RG_insEdges_on_empty_is_empty : forall (A B : Type) (edges : list (RG_Edge A B)),
  _insEdges edges RG_empty R== RG_empty.
Proof.
  intros. pose proof RG_insEdge_on_empty_is_empty. induction edges.
  - firstorder.
  - destruct a as [[from to] lab]. firstorder.
Qed.



Definition cListToEnsemble {A : Type} (az : list A) : Ensemble A :=
  fold_right Ensemble_add (Empty_set A) az
.

(* "big" statement: *)
Theorem RG_mkGraph_any_ins_all_nodes : forall (A B : Type) (nodes : list A) (edges : list (RG_Edge A B)),
  RG_labNodes (RG_mkGraph nodes edges) S== cListToEnsemble nodes.
Proof.
  intros.
  unfold RG_mkGraph.
  rewrite RG_insEdges_does_not_add_nodes.
  rewrite RG_insNodes_any_ins_all_nodes.

  firstorder.
Qed.



Theorem RG_empty_isEmpty : forall (A B : Type), RG_isEmpty (@RG_empty A B).
Proof.
  firstorder.
Qed.



Theorem RG_labNodes_empty_nil : forall (A B : Type),
  RG_labNodes (@RG_empty A B) S== Empty_set A.
Proof.
  firstorder.
Qed.

(* Lemma RG_ins_only_edge_isEmpty : forall (A B : Type) (edge : (RG_Edge A B)),
  _insEdge edge RG_empty R== RG_empty.
Proof.
  intros. unfold RG_equiv. destruct edge as [[from to] lab]. split.
  - firstorder.
  - firstorder.
Qed. *)


Lemma RG_ins_only_edge_isEmpty : forall (A B : Type) (edge : RG_Edge A B) (rg : RG A B),
  RG_isEmpty rg <-> RG_isEmpty (_insEdge edge rg).
Proof.
  intros. destruct edge as [[from to] lab]. firstorder.
Qed.


Lemma RG_ins_only_edges_isEmpty : forall (A B : Type) (edges : list (RG_Edge A B)) (rg : RG A B),
  RG_isEmpty rg <-> RG_isEmpty (_insEdges edges rg).
Proof.
  intros. induction edges; simpl in *.
  - reflexivity.
  - rewrite IHedges. rewrite RG_ins_only_edge_isEmpty. reflexivity.
Qed.

Lemma RG_insNode_not_isEmpty :  forall (A B : Type) (node : A) (rg : RG A B),
  not (RG_isEmpty (_insNode node rg)).
Proof.
  unfold not. intros. unfold _insNode in H. unfold RG_isEmpty in H. destruct (H node).
  firstorder.
Qed.




Theorem RG_insNodes_length_nodes : forall (A B : Type) (nodes : list A) (rg : RG A B),
  length nodes = 0 <-> RG_isEmpty (_insNodes nodes (@RG_empty _ B)).
Proof.
  intros. destruct nodes.
  - firstorder.
  - simpl. split; intros.
    + discriminate H.
    + pose proof RG_insNode_not_isEmpty. unfold not in H0. apply H0 in H. destruct H.
Qed.




Theorem RG_match_empty_is_nothing : forall (A B : Type) (node : A),
  RG_match node (@RG_empty A B) D== ((False, (fun x y => False, node, fun x y => False)), RG_empty).
Proof.
  firstorder.
Qed.





(* Theorem RG_spec4 : forall (A B : Type) (node : A) (nodes : list A) (edges : list (RG_Edge A B)), 
  List.In node nodes -> exists froms tos, RG_match node (RG_mkGraph nodes edges) =
  ((True, (froms, tos)), RG_mkGraph (filter (fun n => negb (node =? n)) nodes) (filter (fun '(from, to) => negb ((from =? node) || (to =? node))) edges)).
(* This is not even a complete specification and it looks like a hard one to prove... *)
Proof.
Admitted. *)





Theorem RG_spec5 : forall (A B : Type) (node : A) (nodes : list A) (edges : list (RG_Edge A B)), 
  not (List.In node nodes) ->
    RG_match node (RG_mkGraph nodes edges) = ((False, (fun x y => False, node, fun x y => False)), RG_mkGraph nodes edges).
Proof.
  intros.
  unfold not in H. unfold RG_match. f_equal.
  - unfold _getFromsAndTos. f_equal.
    +  admit.
    + f_equal.
      -- f_equal.
        ++ admit.
      -- admit.
  - admit.
Admitted.
