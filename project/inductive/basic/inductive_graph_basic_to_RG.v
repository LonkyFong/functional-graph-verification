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


(* Defining Conversion function from IG_basic to RG *)
(* Also states (and eventually proves) that operations on IG_basic are equivalent to those of RG *)



(* Adds a node and its in- and out- going edges (= its IG context) to an RG.
    Assumes that the neighboring nodes exist *)
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

Definition IG_equiv (ig1 ig2 : IG) : Prop :=
    RG_equiv (IG_basic_to_RG ig1) (IG_basic_to_RG ig2)
.

Notation "g1 I== g2" := (IG_equiv g1 g2) (at level 80).



(* TODO: this should relocate to "examples" after big rename *)
Example basic_equivalence_test : (mkGraph [1; 2] []) I== (mkGraph [2; 1] []).
Proof.
    unfold IG_equiv. unfold RG_equiv. firstorder.
Qed.

Example basic_equivalence_test' : (mkGraph [1; 2; 3] [(1, 2); (2, 3)]) I== (mkGraph [2; 1; 3] [(2, 3); (1, 2)]).
Proof.
    unfold IG_equiv. unfold RG_equiv. firstorder.
Qed.




(* Now go to proving that the implementations from IG basic relate to the RG ones *)
(* Filling in all the admitteds, should suffice to show that IG_basic operations are equivalent to RG operations *)
(* Hence, all theorems from one apply to the other *)
(*   {-# MINIMAL empty, isEmpty, match, mkGraph, labNodes #-} *)
Definition IG_basic_Propify_isEmpty (result : bool) : Prop.
Proof.
Admitted.

Definition IG_basic_Propify_matsh (result : option (NatSet.t * NatSet.t) * IG) : (Prop * (Ensemble nat * Ensemble nat)) * RG nat.
Proof.
Admitted.

Definition IG_basic_Propify_labNodes (result : list Node) : Ensemble Node.
Proof.
Admitted.


Theorem IG_basic_empty_relate :
  IG_basic_to_RG empty = RG_empty.
Proof.
Admitted.

Theorem IG_basic_isEmpty_relate : forall (ig : IG),
  IG_basic_Propify_isEmpty (isEmpty ig) = RG_isEmpty (IG_basic_to_RG ig).
Proof.
Admitted.


Theorem IG_basic_matsh_relate : forall (node : Node) (ig : IG),
  IG_basic_Propify_matsh (matsh node ig) = RG_matsh node (IG_basic_to_RG ig).
Proof.
Admitted.

Theorem IG_basic_mkGraph_relate : forall (nodes : list Node) (edges : list (Node * Node)),
  IG_basic_to_RG (mkGraph nodes edges) = RG_mkGraph nodes edges.
Proof.
Admitted.

Theorem IG_basic_labNodes_relate : forall (ig : IG),
  IG_basic_Propify_labNodes (labNodes ig) = RG_labNodes (IG_basic_to_RG ig).
Proof.
Admitted.