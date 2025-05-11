Require Import String.
Require Import Coq.Arith.Arith.
Open Scope string_scope.

Require Import List.
Require Import Bool.
Import ListNotations.

Require Import MyProject.project.inductive.inductive_graph.
Require Import MyProject.project.relational_graph.
Require Import MyProject.project.relational_graph_theory.


(* Defining Conversion from Inductive Graph to Relational Graph, this is a work in progress *)

 

Definition labEdges {A B : Type} (ig : IG A B) : list (LEdge B).
Proof.
Admitted. 

Definition IG_to_RG {A B : Type} (ig : IG A B) : RG A B.
Proof.
    Print labNodes.
    (* list of node labels *)
    pose (nodes := map snd (labNodes ig)).
    (* list of connections made by edges (drop labels)*)
    pose (edges := map (fun (edge : LEdge B) => match edge with | (from, to, lab) => (lookup from ig, lookup to ig) end) (labEdges ig)).
    
    refine {|
        RG_nodes := fun (a : A) =>
                            fold_right (fun (v : A) (acc: Prop) => (a = v) \/ acc) False nodes;
(* This is wrong now, that there are edge labels to consider *)
        RG_edges := fun (a1 a2 : A) l =>
                            fold_right (fun (e : (option A) * (option A)) (acc: Prop) => match e with
                                | (Some from, Some to) => ((a1 = from) /\ (a2 = to)) \/ acc
                                (* This case should never happen *)
                                | _ => acc
                                end) False edges;
                     
        RG_valid := _
    |}.
    RG_valid_prover.
Admitted.


Coercion IG_to_RG : IG >-> RG.


Definition IG_equiv {A : Type} (ig1 ig2 : IG A unit) : Prop :=
    RG_equiv ig1 ig2.

Notation "g1 I== g2" := (IG_equiv g1 g2) (at level 80).
