Require Import MyProject.project.algebraic.algebraic_graph.
Require Import MyProject.project.relational_graph.
(* Notice how this file does not need relational_graph_theory  *)
(* Require Import MyProject.project.relational_graph_theory. *)


(* Defining Conversion from Algebraic Graph to Record Graph *)
Definition RG_unlE_empty {A : Type} : RG_unlE A.
Proof.
    exact RG_empty.
Defined.


Definition RG_unlE_singleton {A : Type} (a : A) : RG_unlE A.
Proof.
    refine {|
        RG_nodes := fun (x : A) => a = x;
        RG_edges := fun x y l => False;
        RG_valid := _
    |}.
    RG_valid_prover.
Defined.


Definition RG_unlE_overlay {A : Type} (rg1 rg2 : RG_unlE A) : RG_unlE A.
Proof.
    refine {|
        RG_nodes := fun A => (rg1.(RG_nodes) A) \/ (rg2.(RG_nodes) A);
        RG_edges := fun A B l => (rg1.(RG_edges) A B l) \/ (rg2.(RG_edges) A B l);
        RG_valid := _
    |}.
    RG_valid_prover_withs rg1 rg2.
Defined.



Definition RG_unlE_connect {A : Type} (rg1 rg2 : RG_unlE A) : RG_unlE A.
Proof.
    let overlay := constr:(RG_unlE_overlay rg1 rg2) in
    refine {|
        RG_nodes := overlay.(RG_nodes);
        RG_edges := fun n1 n2 l => overlay.(RG_edges) n1 n2 l \/ (rg1.(RG_nodes) n1 /\ rg2.(RG_nodes) n2);
        RG_valid := _
    |}.
    RG_valid_prover_withs rg1 rg2.
Defined.




Fixpoint AG_to_RG_unlE {A : Type} (ag : AG A) : RG_unlE A :=
    match ag with
    | Empty => RG_unlE_empty
    | Vertex x => RG_unlE_singleton x
    | Overlay ag1 ag2 => RG_unlE_overlay (AG_to_RG_unlE ag1) (AG_to_RG_unlE ag2)
    | Connect ag1 ag2 => RG_unlE_connect (AG_to_RG_unlE ag1) (AG_to_RG_unlE ag2)
    end
.

(* TODO: this coercion may or may not be good to have *)
Coercion AG_to_RG_unlE : AG >-> RG_unlE.


Definition AG_equiv {A : Type} (ag1 ag2 : AG A) : Prop :=
    RG_equiv (AG_to_RG_unlE ag1) (AG_to_RG_unlE ag2).

Notation "g1 A== g2" := (AG_equiv g1 g2) (at level 80).