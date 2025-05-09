Require Import MyProject.project.algebraic.algebraic_graph.
Require Import MyProject.project.relational_graph.
(* Notice how this file does not need relational_graph_theory  *)
(* Require Import MyProject.project.relational_graph_theory. *)


(* Defining Conversion from Algebraic Graph to Record Graph *)
Definition empty_RG {A : Type} : RG A.
Proof.
    exact RG_empty.
Defined.


Definition singleton_RG {A : Type} (a : A) : RG A.
Proof.
    refine {|
        RG_nodes := fun (x : A) => a = x;
        RG_edges := fun x y => False;
        RG_valid := _
    |}.
    RG_valid_prover.
Defined.


Definition overlay_RG {A : Type} (rg1 rg2 : RG A) : RG A.
Proof.
    refine {|
        RG_nodes := fun A => (rg1.(RG_nodes) A) \/ (rg2.(RG_nodes) A);
        RG_edges := fun A B => (rg1.(RG_edges) A B) \/ (rg2.(RG_edges) A B);
        RG_valid := _
    |}.
    RG_valid_prover_withs rg1 rg2.
Defined.



Definition connect_RG {A : Type} (rg1 rg2 : RG A) : RG A.
Proof.
    let overlay := constr:(overlay_RG rg1 rg2) in
    refine {|
        RG_nodes := overlay.(RG_nodes);
        RG_edges := fun A B => overlay.(RG_edges) A B \/ (rg1.(RG_nodes) A /\ rg2.(RG_nodes) B);
        RG_valid := _
    |}.
    RG_valid_prover_withs rg1 rg2.
Defined.




Fixpoint AG_to_RG {A : Type} (ag : AG A) : RG A :=
    match ag with
    | Empty => empty_RG
    | Vertex x => singleton_RG x
    | Overlay ag1 ag2 => overlay_RG (AG_to_RG ag1) (AG_to_RG ag2)
    | Connect ag1 ag2 => connect_RG (AG_to_RG ag1) (AG_to_RG ag2)
    end
.

(* TODO: this coercion may or may not be good to have *)
Coercion AG_to_RG : AG >-> RG.


Definition AG_equiv {A : Type} (ag1 ag2 : AG A) : Prop :=
    RG_equiv ag1 ag2.

Notation "g1 A== g2" := (AG_equiv g1 g2) (at level 80).