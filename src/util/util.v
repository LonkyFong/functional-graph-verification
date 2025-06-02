Require Import Bool.
Require Import Coq.Arith.Arith.
Require Import List.

Require Import Coq.Sets.Ensembles.
Require Import Setoid Morphisms.

(* Defines miscellaneous utilities useful across the project  *)


(* Custom additional functions for Ensembles. Standard library equivalents may exist,
but they are less transparent and more difficult to work with *)
Definition Ensemble_add {A : Type} (a : A) (en : Ensemble A) : Ensemble A :=
    fun (x : A) => x = a \/ en x.

Definition Ensemble_union {A : Type} (en1 en2 : Ensemble A) : Ensemble A :=
    fun (a : A) => en1 a \/ en2 a.



(* Leads to define "bdestruct", a useful tactic from
Software Foundations, Volume 3: Verified Functional Algorithms, Chapter Perm *)
Lemma eqb_reflect : forall x y, reflect (x = y) (x =? y).
Proof.
    intros x y. apply iff_reflect. symmetry.
    apply Nat.eqb_eq.
Qed.

Lemma ltb_reflect : forall x y, reflect (x < y) (x <? y).
Proof.
    intros x y. apply iff_reflect. symmetry.
    apply Nat.ltb_lt.
Qed.

Lemma leb_reflect : forall x y, reflect (x <= y) (x <=? y).
Proof.
    intros x y. apply iff_reflect. symmetry.
    apply Nat.leb_le.
Qed.

Hint Resolve ltb_reflect leb_reflect eqb_reflect : bdestruct.

Ltac bdestruct X :=
    let H := fresh in let e := fresh "e" in
        evar (e: Prop);
        assert (H: reflect e X); subst e;
        [ auto with bdestruct
        | destruct H as [H|H];
            [ | try first [apply not_lt in H | apply not_le in H]]
        ].
