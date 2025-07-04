Require Import GraphVerification.src.relational.RG.
Require Import GraphVerification.src.algebraic.AG.


(** Defining how an AG converts to an RG *)

(* Conversion for each constructor *)
Definition RG_empty {A : Type} : RG_unlE A :=
    RG_empty.

Definition RG_vertex {A : Type} (a : A) : RG_unlE A.
Proof.
    refine {|
        RG_nodes := fun (x : A) => a = x;
        RG_edges := fun x y l => False;
        RG_valid := _
    |}.
    RG_valid_prover.
Defined.

Definition RG_overlay {A : Type} (rg1 rg2 : RG_unlE A) : RG_unlE A :=
    RG_union rg1 rg2.


Definition RG_connect {A : Type} (rg1 rg2 : RG_unlE A) : RG_unlE A.
Proof.
    let overlay := constr:(RG_overlay rg1 rg2) in
    refine {|
        RG_nodes := overlay.(RG_nodes);
        RG_edges := fun n1 n2 l => overlay.(RG_edges) n1 n2 l \/ (rg1.(RG_nodes) n1 /\ rg2.(RG_nodes) n2);
        RG_valid := _
    |}.
    RG_valid_prover rg1 rg2.
Defined.


(* Putting it all together *)
Fixpoint AG_to_RG {A : Type} (ag : AG A) : RG_unlE A :=
    match ag with
    | AG_empty => RG_empty
    | AG_vertex x => RG_vertex x
    | ag1 +++ ag2 => RG_overlay (AG_to_RG ag1) (AG_to_RG ag2)
    | ag1 *** ag2 => RG_connect (AG_to_RG ag1) (AG_to_RG ag2)
    end.


(* Two AGs are equivalent, if their RGs are equivalent *)
Definition AG_equiv {A : Type} (ag1 ag2 : AG A) : Prop :=
    (AG_to_RG ag1) ==R (AG_to_RG ag2).

Notation "g1 ==A g2" := (AG_equiv g1 g2) (at level 80).