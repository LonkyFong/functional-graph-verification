Require Import String.
Require Import Coq.Arith.Arith.
Open Scope string_scope.

Require Import List.
Require Import Bool.
Import ListNotations.

Require Import MyProject.project.inductive.inductive_graph.
Require Import MyProject.project.relational_graph.
Require Import MyProject.project.relational_graph_theory.

Require Import MyProject.project.util.NatMap.
Require Import MyProject.project.util.NatSet.
Require Import MyProject.project.util.util.

(* Defining Conversion from Inductive Graph to Relational Graph *)
(* 

(* Adds a node and its in- and out- going edges (= its IG context) to an RG.
    Adds the neighbouring nodes, in case they do not exists *)
Definition _extendByContext {B : Type} (node : Node) (froms tos : Adj B) (rg : RG_unlE nat) : RG_unlE nat.
Proof.
    refine {|
        RG_nodes := fun (n : nat) => In n (map snd froms) \/ In n (map snd tos) \/ (cEnsembleAdd node rg.(RG_nodes)) n; 
        RG_edges := fun (n1 n2 : nat) l =>
                                (In n1 (map snd froms) /\ n2 = node)
                                \/ (n1 = node /\ In n2 (map snd tos))
                                \/ rg.(RG_edges) n1 n2 l
                                ;
                     
        RG_valid := _
    |}.
    RG_valid_prover_with rg.
Defined.


(* Adds a node and its in- and out- going edges (= its IG context) to an RG.
    Assumes that the neighboring nodes exist *)
Definition _accTo_RG_unlE {A B : Type} (node : LNode A) (rgIg : RG_unlE nat * IG A B) : RG_unlE nat * IG A B :=
    match node with
    | (node, lab) =>
        match rgIg with
        | (rg, ig) =>
            match IG_match node ig with
            | (Some (froms, _, _, tos), rest) => (_extendByContext node froms tos rg, rest)
            | (None, sameIg)            => (rg, sameIg)
            end
        end
    end
.

(* Looses multi-edges (IGs can have multiple same-label edges), Also looses labels *)
Definition IG_to_RG {A B : Type} (ig : IG A B) : RG_unlE nat :=
    match fold_right _accTo_RG_unlE (RG_empty, ig) (IG_labNodes ig) with
    | (rg, acc) => rg
    end
. *)


(* Definition _extendByContext {A B : Type} (context : Context A B) (rg : RG_unlE nat) : RG_unlE nat.
Proof.
    destruct context as [[[froms node] label] tos].
    refine {|
        RG_nodes := fun (n : nat) => In n (map snd froms) \/ In n (map snd tos) \/ (cEnsembleAdd node rg.(RG_nodes)) n; 
        RG_edges := fun (n1 n2 : nat) l =>
                                (In n1 (map snd froms) /\ n2 = node)
                                \/ (n1 = node /\ In n2 (map snd tos))
                                \/ rg.(RG_edges) n1 n2 l
                                ;
                     
        RG_valid := _
    |}.
    RG_valid_prover_with rg.
Defined. *)


Definition RG_add {A B : Type} (context : Context A B) (rg : RG_unlE nat) : RG_unlE nat.
Proof.
    destruct context as [[[froms node] label] tos].
    refine {|
        RG_nodes := fun (n : nat) => (cEnsembleAdd node rg.(RG_nodes)) n;
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
    IG_ufold _ _ _ RG_add RG_empty ig.






(* Coercion IG_basic_to_RG : IG_basic >-> RG. *)

(* This does not respect the labels for now *)
Definition IG_equiv {A B : Type} (ig1 ig2 : IG A B) : Prop :=
    RG_equiv (IG_to_RG ig1) (IG_to_RG ig2)
.

Notation "g1 I== g2" := (IG_equiv g1 g2) (at level 80).


