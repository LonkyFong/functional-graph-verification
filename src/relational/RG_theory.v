Require Import Setoid Morphisms.

Require Import GraphVerification.src.relational.RG.


(** Stating and proving Lemmas and Theorems about RGs *)


(* "RG_equiv" is an equivalence relation: *)
Instance RG_Equivalence {A B : Type} : Equivalence (@RG_equiv A B).
Proof.
    unfold RG_equiv. split.
    (* Reflexive *)
    - firstorder.
    (* Symmetric *)
    - firstorder.
    (* Transitive *)
    - unfold Transitive. firstorder.
        + apply H1. apply H2. assumption.
        + apply H2. apply H1. assumption.
Qed.



(* Proves a relation derived from RG_equiv (off by just a coercion) is also an equivalence relation *)
Ltac G_derived_equivalence_prover A B f :=
    pose proof (@RG_Equivalence A B) as H;
    destruct H as [Eq_Refl Eq_Symm Eq_Trans]; split;
    [ unfold Reflexive; intros; unfold Reflexive in Eq_Refl; apply Eq_Refl
    | unfold Symmetric; intros; unfold Symmetric in Eq_Symm; apply Eq_Symm; apply H
    | unfold Transitive; intros x y z H H0; intros; unfold Transitive in Eq_Trans; apply (Eq_Trans _ (f y) _);
        [ apply H
        | apply H0
        ]
    ].


(* Some theorems about RG_transpose. Whenever a graphs transpose operation is proven to relate to RG_transpose, these automatically follow *)

Theorem RG_transpose_transpose {A B : Type}: forall (rg : RG A B),
    RG_transpose (RG_transpose rg) ==R rg.
Proof.
    firstorder.   
Qed.

Theorem RG_transpose_same_nodes {A B : Type}: forall (rg : RG A B) n,
    (RG_transpose rg).(RG_nodes) n <-> rg.(RG_nodes) n.
Proof.
    firstorder.
Qed.

Theorem RG_transpose_flips_edges {A B : Type}: forall (rg : RG A B) n1 n2 l,
    (RG_transpose rg).(RG_edges) n1 n2 l <-> rg.(RG_edges) n2 n1 l.
Proof.
    firstorder.
Qed.

Theorem RG_transpose_flips_paths {A B : Type}: forall (rg : RG A B) n1 n2,
    RG_existsPath n1 n2 rg <-> RG_existsPath n2 n1 (RG_transpose rg).
Proof.
    intros.
    apply Operators_Properties.clos_trans_transp_permute.
Qed.
