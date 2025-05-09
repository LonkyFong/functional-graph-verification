Require Import String.
Require Import Coq.Arith.Arith.
Open Scope string_scope.

Require Import List.
Require Import Bool.
Import ListNotations.

Require Import MyProject.project.inductive.basic.inductive_graph_basic.
Require Import MyProject.project.relational_graph.

Require Import Coq.Sets.Ensembles.


(* Defining Conversion from basic Inductive Graph to Relational Graph *)


(* Adds a node and its in- and out- going edges (= its IG context) to an RG.
    Assumes that the neighboring nodes exist *)
Definition _extendByContext (node : Node) (froms tos : NatSet.t) (rg : RG nat) : RG nat.
Proof.
    refine {|
        gr_nodes := fun (n : nat) => n = node \/ NatSet.In n froms \/ NatSet.In n tos \/ rg.(gr_nodes) n;

        gr_edges := fun (n0 n1 : nat) =>
                                (NatSet.In n0 froms /\ n1 = node)
                                \/ (n0 = node /\ NatSet.In n1 tos)
                                \/ rg.(gr_edges) n0 n1
                                ;
                     
        gr_valid := _
    |}.
    unfold valid_cond. pose proof rg.(gr_valid). firstorder.
Defined.


Definition _accTo_RG (node : Node) (rgIg : RG nat * IG) : RG nat * IG :=
    match rgIg with | (rg, ig) =>
        match matsh node ig with
        | (Some (froms, tos), rest) => (_extendByContext node froms tos rg, rest)
        | (None, sameIg)            => (rg, sameIg)
        end
    end
.

Definition IG_basic_to_RG (ig : IG) : RG nat :=
    match fold_right _accTo_RG (RG_empty, ig) (labNodes ig) with
    | (rg, acc) => rg
    end
.


(* Coercion IG_basic_to_RG : IG >-> RG. *)

Definition equiv_IG (ig1 ig2 : IG) : Prop :=
    equiv_G (IG_basic_to_RG ig1) (IG_basic_to_RG ig2)
.

Notation "g1 I== g2" := (equiv_IG g1 g2) (at level 80).


(* Section to make rewrite work with equiv_IG *)

(* Source for rewrite: https://stackoverflow.com/questions/56099646/use-rewrite-tactic-with-my-own-operator-in-coq *)
Require Import Setoid Morphisms.

(* This proof is based on === being an equivalence relation *)
Instance IG_Equivalence_eq : Equivalence equiv_IG.
Proof.
    pose proof (@RG_Equivalence_eq nat). destruct H. split.
    - unfold Reflexive. intros. unfold Reflexive in Equivalence_Reflexive. apply Equivalence_Reflexive.
    - unfold Symmetric. intros. unfold Symmetric in Equivalence_Symmetric. apply Equivalence_Symmetric. apply H.
    - unfold Transitive. intros. unfold Transitive in Equivalence_Transitive. apply (Equivalence_Transitive _ (IG_basic_to_RG y) _).
        + apply H.
        + apply H0.
Qed. 


Example basic_equivalence_test : (mkGraph [1; 2] []) I== (mkGraph [2; 1] []).
Proof.
    unfold equiv_IG. unfold equiv_G. firstorder.
Qed.

Example basic_equivalence_test' : (mkGraph [1; 2; 3] [(1, 2); (2, 3)]) I== (mkGraph [2; 1; 3] [(2, 3); (1, 2)]).
Proof.
    unfold equiv_IG. unfold equiv_G. firstorder.
Qed.



(* Now start defining the basic IG functions in terms of an RG *)
  (* {-# MINIMAL empty, isEmpty, match, mkGraph, labNodes #-} *)


(* Start defining functionality: *)
Definition RG_empty : RG nat :=
    RG_empty.


Definition RG_isEmpty (rg : RG nat) : Prop :=
  RG_isEmpty rg.



(* Helper for matsh *)
Definition _eliminate (node : Node) (rg : RG nat) : RG nat.
Proof.
  refine {|
      gr_nodes :=  Subtract nat (rg.(gr_nodes)) node;
      gr_edges := fun (n0 n1 : nat) => n0 <> node /\ n1 <> node /\  rg.(gr_edges) n0 n1;
      gr_valid := _
  |}.
  unfold valid_cond. pose proof rg.(gr_valid). firstorder.
  - unfold not. intros. inversion H2. congruence.
  - unfold not. intros. inversion H2. congruence.
Defined.

Definition _getFromsAndTos (node : Node) (rg : RG nat) : Prop * (Ensemble nat * Ensemble nat) :=
  (rg.(gr_nodes) node, ((fun (from : nat) => rg.(gr_edges) from node), (fun (to : nat) => rg.(gr_edges) node to)))
.


(* (Ensemble nat * Ensemble nat) is not a relation, it is two _independent_ sets of from- and to- neighbors *)
Definition RG_matsh (node : Node) (rg : RG nat) : (Prop * (Ensemble nat * Ensemble nat)) * RG nat :=
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
  destruct edge as [node0 node1].
    refine {|
      gr_nodes := rg.(gr_nodes);
      gr_edges := fun (n0 n1 : nat) => (n0 = node0 /\ n1 = node1 /\ rg.(gr_nodes) node0 /\ rg.(gr_nodes) node1) \/  rg.(gr_edges) n0 n1;
      gr_valid := _
  |}.
  unfold valid_cond. pose proof rg.(gr_valid). firstorder.
  - congruence.
  - congruence.
Qed.


Definition _insEdges (edges : list (Node * Node)) (rg : RG nat) : RG nat :=
  fold_right _insEdge rg edges.

Definition RG_mkGraph (nodes : list Node) (edges : list (Node * Node)) : RG nat :=
  _insEdges edges (_insNodes nodes RG_empty).
 
Definition RG_labNodes (rg : RG nat) : Ensemble Node :=
  rg.(gr_nodes).
