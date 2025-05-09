Require Import Bool.
Require Import Coq.Arith.Arith.
Require Import List.

Require Import Coq.Sets.Ensembles.


(* Utility things, that don't really belong anywhere else *)

(* This works better in proofs than the library Add for ensembles *)
Definition _customEnsembleAdd {A : Type} (a : A) (en : Ensemble A) : Ensemble A :=
  fun (x : A) => x = a \/ en x
.

Definition _listToEnsemble {A : Type} (az : list A) : Ensemble A :=
  fold_right _customEnsembleAdd (Empty_set A) az
.




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
