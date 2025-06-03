Require Import String.
Require Import Coq.Arith.Arith.
Open Scope string_scope.

Require Import List.
Require Import Bool.
Import ListNotations.

Require Import GraphVerification.src.inductive.inductive_graph.
Require Import GraphVerification.src.inductive.inductive_graph_measure.
Require Import GraphVerification.src.inductive.inductive_graph_measured_algorithms.

Require Import GraphVerification.src.relational_graph.
Require Import GraphVerification.src.relational_graph_theory.

Require Import GraphVerification.src.util.NatMap.
Require Import GraphVerification.src.util.NatSet.
Require Import GraphVerification.src.util.util.

(* Defining how an IG converts to an RG *)


Definition RG_and {A B : Type} (context : Context A B) (rg : RG_unlE nat) : RG_unlE nat.
Proof.
    destruct context as [[[froms node] label] tos].
    refine {|
        RG_nodes := fun (n : nat) => (Ensemble_add node rg.(RG_nodes)) n;
        RG_edges := fun (n1 n2 : nat) l => rg.(RG_edges) n1 n2 l \/
                                           (not (rg.(RG_nodes) node) /\ rg.(RG_nodes) n1 /\ rg.(RG_nodes) n2 /\
                                            ((In n1 (map snd froms) /\ n2 = node)
                                            \/ (n1 = node /\ In n2 (map snd tos))
                                           )
                                           );
         RG_valid := _
    |}.
    RG_valid_prover_with rg.
Defined.




Definition IG_to_RG {A B : Type} (ig : IG A B) : RG_unlE nat :=
    IG_ufold _ _ _ RG_and RG_empty ig.



(* This does not respect the labels for now *)
Definition IG_equiv {A B : Type} (ig1 ig2 : IG A B) : Prop :=
    RG_equiv (IG_to_RG ig1) (IG_to_RG ig2).

Notation "g1 I== g2" := (IG_equiv g1 g2) (at level 80).

