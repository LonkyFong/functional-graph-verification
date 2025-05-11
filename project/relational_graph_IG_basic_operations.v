(* Require Import String.
Require Import Coq.Arith.Arith.
Open Scope string_scope.

Require Import List.
Require Import Bool.
Import ListNotations.

Require Import MyProject.project.util.util.

Require Import MyProject.project.relational_graph.
Require Import MyProject.project.relational_graph_theory.


Require Import Coq.Sets.Ensembles.
Require Import MyProject.project.util.NatSet.


(* Defines the IG_basic functions in terms of an RG (without multigraph) soon to be "OUTCLASSED" by relational_graph_IG_operations*)
  (* {-# MINIMAL empty, isEmpty, match, mkGraph, labNodes #-} *)


(* Start defining functionality: *)
Definition RG_empty : RG nat :=
    RG_empty.


Definition RG_isEmpty (rg : RG nat) : Prop :=
  RG_isEmpty rg.



(* Helper for match *)
(* Removes a node from the nodeset and any edges *)
Definition _eliminate (node : Node) (rg : RG nat) : RG nat.
Proof.
  refine {|
      RG_nodes := Subtract nat rg.(RG_nodes) node;
      RG_edges := fun (n1 n2 : nat) => n1 <> node /\ n2 <> node /\  rg.(RG_edges) n1 n2;
      RG_valid := _
  |}.
  RG_valid_prover_with rg.
  - unfold not. intros. inversion H3. congruence.
  - unfold not. intros. inversion H3. congruence.
Defined.

(* Checks if the node is in the RG (the Prop return) and returns two sets of alls incoming neighbors and outgoing neighbors *)
Definition _getFromsAndTos (node : Node) (rg : RG nat) : Prop * (Ensemble nat * Ensemble nat) :=
  (rg.(RG_nodes) node, ((fun (from : nat) => rg.(RG_edges) from node), (fun (to : nat) => rg.(RG_edges) node to)))
.


(* (Ensemble nat * Ensemble nat) is not a relation, it is two _independent_ sets of from- and to- neighbors *)
Definition RG_match (node : Node) (rg : RG nat) : (Prop * (Ensemble nat * Ensemble nat)) * RG nat :=
  (_getFromsAndTos node rg, _eliminate node rg)
.



Definition _add (node : Node) (fromsTos : (NatSet.t * NatSet.t)) (rg : RG nat) : RG nat :=
  match fromsTos with | (froms, tos) =>
    _extendByContext node froms tos rg
  end
.


Definition _insNode (node : Node) (rg : RG nat) : RG nat :=
  _add node (NatSet.empty, NatSet.empty) rg.
  

Definition _insNodes (nodes : list Node) (rg : RG nat) : RG nat :=
  fold_right _insNode rg nodes.


(* If one of the nodes of the edge does not exist, nothing happens *)
Definition _insEdge (edge : (Node * Node)) (rg : RG nat) : RG nat.
Proof.
  destruct edge as [node1 node2].
    refine {|
      RG_nodes := rg.(RG_nodes);
      RG_edges := fun (n1 n2 : nat) => (n1 = node1 /\ n2 = node2 /\ rg.(RG_nodes) node1 /\ rg.(RG_nodes) node2) \/  rg.(RG_edges) n1 n2;
      RG_valid := _
  |}.
  RG_valid_prover_with rg.
  - congruence.
  - congruence.
Defined.


Definition _insEdges (edges : list (Node * Node)) (rg : RG nat) : RG nat :=
  fold_right _insEdge rg edges.

Definition RG_mkGraph (nodes : list Node) (edges : list (Node * Node)) : RG nat :=
  _insEdges edges (_insNodes nodes RG_empty).
 

Definition RG_labNodes (rg : RG nat) : Ensemble Node :=
  rg.(RG_nodes). *)