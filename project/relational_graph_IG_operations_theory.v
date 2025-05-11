Require Import String.
Require Import Coq.Arith.Arith.
Open Scope string_scope.

Require Import List.
Require Import Bool.
Import ListNotations.

Require Import MyProject.project.util.util.

(* Require Import MyProject.project.relational_graph.
Require Import MyProject.project.relational_graph_theory. *)
Require Import MyProject.project.relational_graph_IG_operations.

Require Import Coq.Sets.Ensembles.

Require Import MyProject.project.util.NatSet.


Open Scope nat_scope.

(* Specifies behavior of IH functions on an (edge-label compatible) RG via equational specification *)


(* Here start "meaningful statements" *)

(* 5 statements on inserting (helpers for mkGraph): update, insEdge, insEdges, insNode, insNodes *)

Lemma RG_insEdge_does_not_add_node : forall (A B : Type) (edge : (Edge A B)) (rg : RG A B),
  RG_labNodes (_insEdge edge rg) = RG_labNodes rg.
Proof.
Admitted.
  (* intros. simpl. unfold RG_labNodes. unfold _insEdge. destruct edge. simpl. reflexivity. *)


Lemma RG_insEdges_does_not_add_nodes : forall (A B : Type) (edges : list (@Edge A B)) (rg : RG A B),
  RG_labNodes (_insEdges edges rg) = RG_labNodes rg.
Proof.
Admitted.


Lemma RG_insNode_any_ins_node : forall (A B : Type) (node : A) (rg : RG A B),
  RG_labNodes (_insNode node rg) = _customEnsembleAdd node (RG_labNodes rg).
Proof.
Admitted.




Lemma RG_insNodes_any_ins_all_nodes : forall (A B : Type) (nodes : list A) (rg : RG A B),
  RG_labNodes (_insNodes nodes rg) = Union A (_listToEnsemble nodes) (RG_labNodes rg).
Proof.
Admitted.



Lemma RG_insEdge_on_empty_is_empty : forall (A B : Type) (edge : (Edge A B)),
  _insEdge edge RG_empty = RG_empty.
Proof.
Admitted.


Lemma RG_insEdges_on_empty_is_empty : forall (A B : Type) (edges : list (Edge A B)),
  _insEdges edges RG_empty = RG_empty.
(* This proof is very similar to "insEdges_does_not_add_nodes", but using it here it is more complicated than just doing it again  *)
Proof.
Admitted.



(* "big" statement: *)
Theorem RG_mkGraph_any_ins_all_nodes : forall (A B : Type) (nodes : list A) (edges : list (Edge A B)),
  RG_labNodes (RG_mkGraph nodes edges) = _listToEnsemble nodes.
Proof.
Admitted.


Theorem RG_empty_isEmpty : forall (A B : Type), RG_isEmpty (@RG_empty A B).
Proof.
  compute. reflexivity.
Qed.

Theorem RG_labNodes_empty_nil : forall (A B : Type), RG_labNodes (@RG_empty A B) = Empty_set A.
Proof.
Admitted.



Theorem RG_non_empty_isEmpty_false : forall (A B : Type) (nodes : list A) (edges : list (Edge A B)),
  length nodes <> 0 <-> not (RG_isEmpty ((RG_mkGraph nodes edges))).
Proof.
Admitted.




Theorem RG_match_empty_is_nothing : forall (A B : Type) (node : A),
  RG_match node (@RG_empty A B) = ((False, (fun x y => False, node, fun x y => False)), RG_empty).
Proof.
Admitted.





(* Theorem RG_spec4 : forall (A B : Type) (node : A) (nodes : list A) (edges : list (Edge A B)), 
  List.In node nodes -> exists froms tos, RG_match node (RG_mkGraph nodes edges) =
  ((True, (froms, tos)), RG_mkGraph (filter (fun n => negb (node =? n)) nodes) (filter (fun '(from, to) => negb ((from =? node) || (to =? node))) edges)).
(* This is not even a complete specification and it looks like a hard one to prove... *)
Proof.
Admitted. *)


Theorem RG_spec5 : forall (A B : Type) (node : A) (nodes : list A) (edges : list (Edge A B)), 
  not (List.In node nodes) -> RG_match node (RG_mkGraph nodes edges) = ((False, (fun x y => False, node, fun x y => False)), RG_mkGraph nodes edges).
Proof.
Admitted.