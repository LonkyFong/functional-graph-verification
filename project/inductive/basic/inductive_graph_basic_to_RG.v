Require Import String.
Require Import Coq.Arith.Arith.
Open Scope string_scope.

Require Import List.
Require Import Bool.
Import ListNotations.
Require Import Coq.Sets.Ensembles.


Require Import MyProject.project.util.util.
Require Import MyProject.project.util.NatSet.

Require Import MyProject.project.inductive.basic.inductive_graph_basic.
Require Import MyProject.project.relational_graph.
Require Import MyProject.project.relational_graph_theory.
Require Import MyProject.project.relational_graph_IG_basic_operations.


(* Defining Conversion function from IG_basic to RG (going towards a model-based approach) *)
(* Also states (and eventually proves) that operations on IG_basic are equivalent to those of RG *)



(* Adds a node and its in- and out- going edges (= its IG context) to an RG.
    Assumes that the neighboring nodes exist *)
Definition _accTo_RG (node : Node) (rgIg : RG nat * IG_basic) : RG nat * IG_basic :=
    match rgIg with | (rg, ig) =>
        match IG_basic_match node ig with
        | (Some (froms, tos), rest) => (_extendByContext node froms tos rg, rest)
        | (None, sameIg)            => (rg, sameIg)
        end
    end
.

Definition IG_basic_to_RG (ig : IG_basic) : RG nat :=
    match fold_right _accTo_RG (RG_empty, ig) (IG_basic_labNodes ig) with
    | (rg, acc) => rg
    end
.


(* Coercion IG_basic_to_RG : IG_basic >-> RG. *)

Definition IG_basic_equiv (ig1 ig2 : IG_basic) : Prop :=
    RG_equiv (IG_basic_to_RG ig1) (IG_basic_to_RG ig2)
.

Notation "g1 I== g2" := (IG_basic_equiv g1 g2) (at level 80).





(* Now go to proving that the implementations from IG basic relate to the RG ones *)
(* Filling in all the admitteds, should suffice to show that IG_basic operations are equivalent to RG operations *)
(* Hence, all theorems from one apply to the other *)
(*   {-# MINIMAL empty, isEmpty, match, mkGraph, labNodes #-} *)
Definition IG_basic_Propify_isEmpty (result : bool) : Prop.
Proof.
Admitted.

Definition IG_basic_Propify_matsh (result : option (NatSet.t * NatSet.t) * IG_basic) : (Prop * (Ensemble nat * Ensemble nat)) * RG nat.
Proof.
Admitted.

Definition IG_basic_Propify_labNodes (result : list Node) : Ensemble Node.
Proof.
Admitted.


Theorem IG_basic_empty_relate :
  IG_basic_to_RG IG_basic_empty = RG_empty.
Proof.
Admitted.

Theorem IG_basic_isEmpty_relate : forall (ig : IG_basic),
  IG_basic_Propify_isEmpty (IG_basic_isEmpty ig) = RG_isEmpty (IG_basic_to_RG ig).
Proof.
Admitted.


Theorem IG_basic_match_relate : forall (node : Node) (ig : IG_basic),
  IG_basic_Propify_matsh (IG_basic_match node ig) = RG_match node (IG_basic_to_RG ig).
Proof.
Admitted.

Theorem IG_basic_mkGraph_relate : forall (nodes : list Node) (edges : list (Node * Node)),
  IG_basic_to_RG (IG_basic_mkGraph nodes edges) = RG_mkGraph nodes edges.
Proof.
Admitted.

Theorem IG_basic_labNodes_relate : forall (ig : IG_basic),
  IG_basic_Propify_labNodes (IG_basic_labNodes ig) = RG_labNodes (IG_basic_to_RG ig).
Proof.
Admitted.