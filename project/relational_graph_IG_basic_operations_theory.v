Require Import String.
Require Import Coq.Arith.Arith.
Open Scope string_scope.

Require Import List.
Require Import Bool.
Import ListNotations.

Require Import MyProject.project.util.util.
Require Import MyProject.project.inductive.basic.inductive_graph_basic.

Require Import MyProject.project.relational_graph.
Require Import MyProject.project.relational_graph_theory.
Require Import MyProject.project.relational_graph_IG_basic_operations.

Require Import Coq.Sets.Ensembles.

Require Import MyProject.project.util.NatSet.


Open Scope nat_scope.

(* Specifies behavior of IH functions on an RG via equational specification *)


(* Here start "meaningful statements" *)

(* 5 statements on inserting (helpers for mkGraph): update, insEdge, insEdges, insNode, insNodes *)

Lemma RG_insEdge_does_not_add_node : forall (edge : (Node * Node)) (rg : RG nat),
  RG_labNodes (_insEdge edge rg) = RG_labNodes rg.
Proof.
  intros. simpl. unfold RG_labNodes. unfold _insEdge. destruct edge. simpl. reflexivity.
Qed.


Lemma RG_insEdges_does_not_add_nodes : forall (edges : list (Node * Node)) (rg : RG nat),
  RG_labNodes (_insEdges edges rg) = RG_labNodes rg.
Proof.
Admitted.


Lemma RG_insNode_any_ins_node : forall (node : Node) (rg : RG nat),
  RG_labNodes (_insNode node rg) = _customEnsembleAdd node (RG_labNodes rg).
Proof.
Admitted.




Lemma RG_insNodes_any_ins_all_nodes : forall (nodes : list Node) (rg : RG nat),
  RG_labNodes (_insNodes nodes rg) = Union nat (_listToEnsemble nodes) (RG_labNodes rg).
Proof.
Admitted.



Lemma RG_insEdge_on_empty_is_empty : forall (edge : Node * Node),
  _insEdge edge RG_empty = RG_empty.
Proof.
Admitted.


Lemma RG_insEdges_on_empty_is_empty : forall (edges : list (Node * Node)),
  _insEdges edges RG_empty = RG_empty.
(* This proof is very similar to "insEdges_does_not_add_nodes", but using it here it is more complicated than just doing it again  *)
Proof.
Admitted.



(* "big" statement: *)
Theorem RG_mkGraph_any_ins_all_nodes : forall (nodes : list Node) (edges : list (Node * Node)),
  RG_labNodes (RG_mkGraph nodes edges) = _listToEnsemble nodes.
Proof.
Admitted.


Theorem RG_empty_isEmpty : RG_isEmpty RG_empty.
Proof.
  compute. reflexivity.
Qed.

Theorem RG_labNodes_empty_nil : RG_labNodes RG_empty = Empty_set nat.
Proof.
Admitted.



Theorem RG_non_empty_isEmpty_false : forall (nodes : list Node) (edges : list (Node * Node)),
  length nodes <> 0 <-> not (RG_isEmpty ((RG_mkGraph nodes edges))).
Proof.
Admitted.




Theorem RG_matsh_empty_is_nothing : forall (node : Node),
  RG_matsh node RG_empty = ((False, (Empty_set nat, Empty_set nat)), RG_empty).
Proof.
Admitted.



Theorem RG_spec4 : forall (node : Node) (nodes : list Node) (edges : list (Node * Node)), 
  List.In node nodes -> exists froms tos, RG_matsh node (RG_mkGraph nodes edges) =
  ((True, (froms, tos)), RG_mkGraph (filter (fun n => negb (node =? n)) nodes) (filter (fun '(from, to) => negb ((from =? node) || (to =? node))) edges)).
(* This is not even a complete specification and it looks like a hard one to prove... *)
Proof.
Admitted.


Theorem RG_spec5 : forall (node : Node) (nodes : list Node) (edges : list (Node * Node)), 
  not (List.In node nodes) -> RG_matsh node (RG_mkGraph nodes edges) = ((False, (Empty_set nat, Empty_set nat)), RG_mkGraph nodes edges).
Proof.
Admitted.