Require Export FMaps.
Require Export FMapAVL.

Require Import Lia.
Require Import Arith.
Require Import GraphVerification.src.util.util.

(* Instantiate an FMap module, such that it is the same across the whole project *)

Definition Node := Nat_as_OT.t.

(* Uses the quick AVL-tree variant *)
Module NatMap := FMapAVL.Make(Nat_as_OT).

(* Library of useful lemmas about maps *)
Module MFacts := WFacts_fun Nat_as_OT NatMap.
(* More useful lemmas about maps *)
Module MProps := WProperties_fun Nat_as_OT NatMap.

Module OMProps := OrdProperties NatMap.




(* This proof is adapted from the link below. This is something that should be in stdlib *)
(* https://github.com/rocq-prover/stdlib/blob/master/theories/FSets/FMapFacts.v *)
(* This is correct, but extremely slow for coq to check.
If a list is used as the FMap backend, checking is much faster *)
Lemma NatMap_cardinal_Add_In:
    forall (A : Type) (m m' : NatMap.t A) x e, NatMap.In x m -> MProps.Add x e m m' -> NatMap.cardinal m' = NatMap.cardinal m.
Proof.
    assert (forall {A : Type} (k : Node) (e : A ) m, NatMap.MapsTo k e m -> MProps.Add k e (NatMap.remove k m) m) as remove_In_Add. {
        intros. unfold MProps.Add.
        intros.
        rewrite MFacts.add_o.
        destruct (MFacts.eq_dec k y).
        - apply NatMap.find_1. rewrite <- MFacts.MapsTo_m; [exact H|assumption|reflexivity|reflexivity].
        - rewrite MFacts.remove_neq_o by assumption. reflexivity.
    }
    intros.
    assert (NatMap.Equal (NatMap.remove x m) (NatMap.remove x m')). {
        intros y. rewrite 2!MFacts.remove_o.
        destruct (MFacts.eq_dec x y).
        - reflexivity.
        - unfold MProps.Add in H0. rewrite H0.
        rewrite MFacts.add_neq_o by assumption. reflexivity.
    }
    apply MProps.Equal_cardinal in H1.
    rewrite 2!MProps.cardinal_fold.
    destruct H as (e' & H).
    rewrite MProps.fold_Add with (eqA:=eq) (m1:=NatMap.remove x m) (m2:=m) (k:=x) (e:=e');
    try now (compute; auto).
    2:apply NatMap.remove_1; reflexivity.
    2:apply remove_In_Add; assumption.
    rewrite MProps.fold_Add with (eqA:=eq) (m1:=NatMap.remove x m') (m2:=m') (k:=x) (e:=e);
    try now (compute; auto).
    - rewrite <- 2!MProps.cardinal_fold. congruence.
    - apply NatMap.remove_1. reflexivity.
    - apply remove_In_Add.
        apply NatMap.find_2. unfold MProps.Add in H0. rewrite H0.
        rewrite MFacts.add_eq_o; reflexivity.
Qed.

Lemma NatMap_add_value_does_not_matter_for_cardinality : forall {A : Type} (node : Node) (c c' : A) (m : NatMap.t A),
    NatMap.cardinal (NatMap.add node c m) = NatMap.cardinal (NatMap.add node c' m).
Proof.
    intros.
    pose proof NatMap_cardinal_Add_In.
    apply (H _ _ _ node c).
    - apply MFacts.add_in_iff. left. reflexivity.
    - unfold MProps.Add. intros. rewrite MFacts.add_o. rewrite MFacts.add_o. rewrite MFacts.add_o. destruct (MProps.F.eq_dec node y).
        + reflexivity.
        + reflexivity.
Qed.


Lemma NatMap_map_find_some_remove_minusOnes_cardinality : forall {A : Type} (key : Node) (map : NatMap.t A),
    (exists x, NatMap.find key map = Some x) -> (S (NatMap.cardinal (NatMap.remove key map)) = NatMap.cardinal map).
Proof.
    intros.
    pose proof MProps.cardinal_2.
    destruct H eqn:hu.
    assert (~ NatMap.In key (NatMap.remove key map)). {
        unfold not. intros.
        apply MFacts.remove_in_iff in H1.
        destruct H1.
        destruct H1.
        reflexivity.

    }
    apply (H0 _ _ map _ x) in H1.
    - rewrite <- H1. reflexivity.
    - unfold MProps.Add. 

    
    unfold MProps.Add. intros. bdestruct (y =? key).
    + rewrite H2. rewrite e. assert (key = key). {
        reflexivity.
    }  pose proof MFacts.add_eq_o. apply (H4 A (NatMap.remove (elt:=A) key map) _ _ x) in H3. rewrite H3. reflexivity.
    + pose proof MFacts.add_neq_o. assert (key <> y). {lia. } apply (H3 A (NatMap.remove (elt:=A) key map) _ _ x) in H4. rewrite H4.
        pose proof MFacts.remove_neq_o. assert (key <> y). {lia. }  apply (H5 A map _ _) in H6. rewrite H6. reflexivity.
Defined.


Lemma NatMap_MapsTo_same_key_same_value : forall {A : Type} (k : Node) (v v' : A) (m : NatMap.t A),
    NatMap.MapsTo k v m -> NatMap.MapsTo k v' m -> v = v'.
Proof.
    intros.
    apply MFacts.find_mapsto_iff in H. apply MFacts.find_mapsto_iff in H0.
    rewrite H0 in H. inversion H. reflexivity.
Qed.


Lemma NatMap_find_some_add_some_idem : forall {A : Type} (k : Node) (v : A) (m : NatMap.t A),
    NatMap.find k m = Some v -> NatMap.Equal m (NatMap.add k v m).
Proof.
    intros.
    apply MFacts.find_mapsto_iff in H.
    apply MFacts.Equal_mapsto_iff. intros. rewrite MFacts.add_mapsto_iff.
    bdestruct (k =? k0).
    - subst. firstorder.
        ++ left.
            rewrite (NatMap_MapsTo_same_key_same_value _ _ _ _ H H0). auto.
        ++ subst. assumption.
    - firstorder.
Qed.

Lemma NatMap_In_exists_MapsTo_iff : forall (A : Type) (x : Node) (m : NatMap.t A),
    NatMap.In x m <-> exists y, NatMap.MapsTo x y m.
Proof.
    firstorder.
Qed.

Lemma NatMap_MapsTo_then_In : forall (A : Type) (x : Node) (y : A) (m : NatMap.t A),
    NatMap.MapsTo x y m -> NatMap.In x m. 
Proof.
    firstorder.
Qed.


Lemma NatMap_is_empty_Equal_empty_iff : forall (A : Type) (m : NatMap.t A), 
    NatMap.is_empty m = true <-> NatMap.Equal m (NatMap.empty _).
Proof.
    intros.
    unfold NatMap.Equal.
    rewrite <- MFacts.is_empty_iff.
    unfold NatMap.Empty.
    unfold NatMap.Raw.Proofs.Empty.
    setoid_rewrite MFacts.find_mapsto_iff.
    firstorder.
    - destruct (NatMap.find y m) eqn:found.
        + firstorder.
        + firstorder.
    - rewrite H. compute. intros. inversion H0.
Qed.

Lemma _not_NatMap_Empty_is_empty_false : forall (A : Type) (m : NatMap.t A),
    not (NatMap.Empty m) <-> NatMap.is_empty m = false.
Proof.
    intros. unfold not. rewrite MFacts.is_empty_iff. destruct (NatMap.is_empty m) eqn:cond.
    - firstorder. congruence.
    - firstorder. congruence.
Qed.