Require Import String.
Require Import Coq.Arith.Arith.
Open Scope string_scope.

Require Import List.
Require Import Bool.
Import ListNotations.

Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Sets.Ensembles.

Require Import MyProject.project.relational_graph.

(* Record RG (t : Type) := {
    gr_nodes : Ensemble t;
    gr_edges : relation t;
    gr_valid : valid_cond gr_nodes gr_edges
}. *)

(* Record Context' (A B : Type) := {
    labNodes : list (A * B);
    labEdges : list (LEdge B)
}.

Record MContext' (A B : Type) := {
    mcontext : option (Context' A B)
}.

Record Decomp'_RG (A B : Type) := {
    mcontext' : MContext' A B;
    rg_rest : RG A B
}. *)

Definition empty_RG {A : Type} : RG A.
Proof.
    refine ({|
        gr_nodes := fun (a : A) => False;
        gr_edges := fun (a b : A) => False;
        gr_valid := _
    |}).
    compute. auto.
Qed.

Definition isEmpty_RG {A : Type} (g : RG A) : Prop :=
    forall (a : A), g.(gr_nodes) a = False.

(* This seems impossible, since one needs to "computationally read the RG", which Prop does not allow *)
Fail Definition matsh_RG {A : Type} (g : RG A) (n : A) : (option (Ensemble A * Ensemble A) * RG A) :=
    match g.(gr_nodes) n with
        | True => (Some (g.(gr_nodes), g.(gr_nodes)), g)
        | False => (None, g)
    end.

Definition mkGraph_RG {A B : Type} (nodes : list A) (edges : list (A * A)) : RG A.

Definition labNodes_RG {A B : Type} (g : RG A) : list (A).


