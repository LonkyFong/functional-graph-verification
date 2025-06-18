Require Import MSets.

(** Instantiate an FSet module, such that it is the same across the whole project
    Also proves some generally useful lemmas about MSets *)


Definition Node := Nat_as_OT.t.

(* Uses the quick AVL-tree variant *)
Module NatSet := MSetAVL.Make(Nat_as_OT).
Module SProps := EqProperties(NatSet).

(* Custom additional function for NatSets "fromList" *)
Definition NatSet_fromList (l : list Node) : NatSet.t :=
    fold_right NatSet.add NatSet.empty l.




Lemma NatSet_In_is_In_elements : forall (x : Node) (s : NatSet.t),
    NatSet.In x s <-> In x (NatSet.elements s).
Proof.
    intros. rewrite <- NatSet.elements_spec1. rewrite SetoidList.InA_alt. firstorder. subst. auto.
Qed.

Lemma NatSet_NoDup_elements : forall (s : NatSet.t),
    NoDup (NatSet.elements s).
Proof.
    intros. pose proof (NatSet.elements_spec2w s). induction (NatSet.elements s).
    - apply NoDup_nil.
    - inversion H. apply NoDup_cons.
        + unfold not in *. intros. apply H2. apply SetoidList.InA_alt. exists a. auto.
        + apply IHl. assumption.
Qed.
