Require Import Bool.
Require Import Coq.Arith.Arith.
Require Import List.

Require Import Coq.Sets.Ensembles.
Require Import Setoid Morphisms.


(* Utility things, that don't really belong anywhere else *)


(* Defining my own Ensemble operations, as the library ones are really clunky and untransparent *)

(* This works better in proofs than the library Add for ensembles *)
Definition cEnsembleAdd {A : Type} (a : A) (en : Ensemble A) : Ensemble A :=
  fun (x : A) => x = a \/ en x
.

Definition cEnsembleUnion {A : Type} (en1 en2 : Ensemble A) : Ensemble A :=
  fun (a : A) => en1 a \/ en2 a
.


Definition cListToEnsemble {A : Type} (az : list A) : Ensemble A :=
  fold_right cEnsembleAdd (Empty_set A) az
.

Definition cEnsemble_equiv {A : Type} (en1 en2 : Ensemble A) : Prop :=
  forall a, en1 a <-> en2 a
.

Notation "en1 S== en2" := (cEnsemble_equiv en1 en2) (at level 100, right associativity).

Instance Ensemble_Equivalence {A : Type} : Equivalence (@cEnsemble_equiv A).
Proof.
  unfold cEnsemble_equiv. firstorder.
Qed.




(* Lemma fold_right_preserves_invariant:
  forall (A B C : Type) (f : A -> B -> B) (g : B -> C),
    (forall a b, g (f a b) = g b) ->
    forall l b0, g (fold_right f b0 l) = g b0.
Proof.
  intros. induction l; simpl.
  - reflexivity.
  - rewrite H. apply IHl.
Qed.
 *)




(* This is from software foundations. Eventually, I will move this somewhere else *)
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
       [ | try first [apply not_lt in H | apply not_le in H]]].
