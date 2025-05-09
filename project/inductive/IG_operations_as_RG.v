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
    RG_nodes : Ensemble t;
    RG_edges : relation t;
    RG_valid : valid_cond RG_nodes RG_edges
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
        RG_nodes := fun (a : A) => False;
        RG_edges := fun (a b : A) => False;
        RG_valid := _
    |}).
    compute. auto.
Qed.

Definition isEmpty_RG {A : Type} (g : RG A) : Prop :=
    forall (a : A), g.(RG_nodes) a = False.

(* This seems impossible, since one needs to "computationally read the RG", which Prop does not allow *)
Fail Definition matsh_RG {A : Type} (g : RG A) (n : A) : (option (Ensemble A * Ensemble A) * RG A) :=
    match g.(RG_nodes) n with
        | True => (Some (g.(RG_nodes), g.(RG_nodes)), g)
        | False => (None, g)
    end.

Definition mkGraph_RG {A B : Type} (nodes : list A) (edges : list (A * A)) : RG A.

Definition labNodes_RG {A B : Type} (g : RG A) : list (A).


