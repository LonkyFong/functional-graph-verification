Require Import Recdef.
Require Import Lia.

Require Import Arith.
Require Import Wf_nat.
Require Import List.
Require Import Wellfounded.
Require Import Lexicographic_Product.
Require Import OrderedType.
Require Import OrderedTypeEx.

Import ListNotations.
Require Import Inverse_Image.
Require Import Relation_Operators.

Require Import GraphVerification.src.util.util.
Require Import GraphVerification.src.util.NatMap.
Require Import GraphVerification.src.inductive.IG.

(** Stating and proving Lemmas and Theorems about measuring the size of an IG.
    These are the only proofs that the last remaining computational functions on IGs need to prove their termination.
    Main results are:
    - IG_match_returns_node
    - IG_match_none_returns_graph
    - IG_match_decreases_IG_noNodes
    - IG_matchAny_decreases_IG_noNodes
    *)


Lemma IG_labNodes_len_cardinal : forall (A B : Type) (ig : IG A B),
    IG_noNodes ig = NatMap.cardinal ig.
Proof.
    intros. unfold IG_noNodes. unfold IG_labNodes. rewrite map_length.
    rewrite NatMap.cardinal_1. reflexivity. 
Qed.

Lemma IG_match_returns_node : forall (A B : Type) (query : Node) (c : Context A B) (ig i : IG A B),
    IG_match query ig = (Some c, i)
        -> let '(_, hit, _, _) := c in query = hit.
Proof.
    destruct_context c. intros. unfold IG_match in H. destruct (NatMap.find query ig).
    - unfold _cleanSplit in H. destruct_context' c. inversion H. reflexivity. 
    - inversion H.
Qed.


Lemma IG_match_none_returns_graph : forall (A B : Type) (query : Node) (ig i : IG A B),
    IG_match query ig = (None, i) -> ig = i.
Proof.
    intros. unfold IG_match in H. destruct (NatMap.find query ig).
    - destruct (_cleanSplit query c (NatMap.remove query ig)). inversion H.
    - inversion H. reflexivity.
Qed.



Lemma _IG_updateEntry_does_not_change_cardinality : forall {A B : Type} (node : Node) (f : Context' A B -> Context' A B) (ig : IG A B), 
    NatMap.cardinal (_updateEntry node f ig) = NatMap.cardinal ig.
Proof.
    intros. unfold _updateEntry.

    destruct (NatMap.find node ig) eqn:split.
    - apply NatMap_find_some_add_some_idem in split.
        rewrite split at 2.
        apply NatMap_add_value_does_not_matter_for_cardinality.
    - reflexivity.
Qed.


Lemma _IG_updAdj_does_not_change_cardinality : forall {A B : Type} (adj : Adj B) (f : B -> Context' A B -> Context' A B) (ig : IG A B), 
    NatMap.cardinal (_updAdj adj f ig) = NatMap.cardinal ig.
Proof.
    intros.
    unfold _updAdj.
    induction adj; simpl.
    - reflexivity.
    - rewrite <- IHadj. destruct a.
        rewrite _IG_updateEntry_does_not_change_cardinality. reflexivity.
Qed.


Lemma _IG_match_minusOnes_cardinality : forall (A B : Type) (n : Node) (c : Context A B) (ig rest : IG A B),
    IG_match n ig = (Some c, rest) -> NatMap.cardinal ig = S (NatMap.cardinal rest).
Proof.
    intros.
    apply IG_match_returns_node in H as s. destruct_context c. subst.
    unfold IG_match in H. destruct (NatMap.find node ig) eqn:find.
    - destruct (_cleanSplit node c (NatMap.remove node ig)) eqn:split.
        inversion H. subst.
        unfold _cleanSplit in split.
        destruct_context' c.
        inversion split.
        clear split H1.

        rewrite !_IG_updAdj_does_not_change_cardinality.
        apply symmetry.
        apply NatMap_map_find_some_remove_minusOnes_cardinality.

        exists (froms', label', tos').
        apply find.
    - inversion H.
Qed.



Lemma _IG_match_minusOnes_IG_noNodes : forall (A B : Type) (n : Node) (c : Context A B) (ig rest : IG A B),
    IG_match n ig = (Some c, rest) -> IG_noNodes ig = S (IG_noNodes rest).
Proof.
    intros. apply _IG_match_minusOnes_cardinality in H.
    rewrite !IG_labNodes_len_cardinal.
    assumption.
Qed.


Theorem IG_match_decreases_IG_noNodes : forall (A B : Type) (n : Node) (c : Context A B) (ig rest : IG A B),
    IG_match n ig = (Some c, rest) -> IG_noNodes rest < IG_noNodes ig.
Proof.
    intros.
    apply _IG_match_minusOnes_IG_noNodes in H. lia.
Qed.


Theorem IG_matchAny_decreases_IG_noNodes : forall (A B : Type) (c : Context A B) (ig rest : IG A B),
    IG_matchAny ig = (Some c, rest) -> IG_noNodes rest < IG_noNodes ig.
Proof.
    intros. unfold IG_matchAny in H. destruct (IG_labNodes ig) eqn:labNodes.
    - inversion H.
    - apply IG_match_decreases_IG_noNodes in H. assumption.
Qed.

