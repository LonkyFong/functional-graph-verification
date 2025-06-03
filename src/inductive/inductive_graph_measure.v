Require Import Recdef.
Require Import Lia.

Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Lists.List.
Require Import Coq.Wellfounded.Wellfounded.
Require Import Coq.Wellfounded.Lexicographic_Product.
Require Import Coq.Structures.OrderedType.
Require Import Coq.Structures.OrderedTypeEx.

Import ListNotations.
Require Import Coq.Wellfounded.Inverse_Image.
Require Import Coq.Relations.Relation_Operators.


Require Import GraphVerification.src.util.util.
Require Import GraphVerification.src.util.NatMap.
Require Import GraphVerification.src.inductive.inductive_graph.

(* Stating and proving Lemmas and Theorems about measuring the size of an IG.
These are the only proofs that the last remaining computational functions on IGs need to prove termination.
*)

(* Lemmas and Theorems try to have only the context as an argument, and break it up internally, and this allows proof to do this too *)
Ltac destruct_context c := destruct c as [[[froms node] label] tos].


Lemma IG_labNodes_len_cardinal : forall (A B : Type) (ig : IG A B),
    IG_noNodes ig = NatMap.cardinal ig.
Proof.
    intros. unfold IG_noNodes. unfold IG_labNodes. rewrite map_length.
    rewrite NatMap.cardinal_1. reflexivity. 
Qed.

Lemma IG_match_returns_node : forall (A B : Type) (query : Node) (c : Context A B) (ig i : IG A B),
    IG_match query ig = (Some c, i) -> let '(_, hit, _, _) := c in query = hit.
Proof.
    destruct_context c. intros. unfold IG_match in H. destruct (NatMap.find query ig).
    - unfold _cleanSplit in H. destruct c as [[fromss labell] toss]. inversion H. reflexivity. 
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
        destruct c as [[fromss labell] toss].
        inversion split.
        clear split H1.

        rewrite !_IG_updAdj_does_not_change_cardinality.
        apply symmetry.
        apply NatMap_map_find_some_remove_minusOnes_cardinality.

        exists (fromss, labell, toss).
        apply find.
    - inversion H.
Qed.



Lemma _IG_match_minusOnes_IGnoNodes : forall (A B : Type) (n : Node) (c : Context A B) (ig rest : IG A B),
    IG_match n ig = (Some c, rest) -> IG_noNodes ig = S (IG_noNodes rest).
Proof.
    intros. apply _IG_match_minusOnes_cardinality in H.
    rewrite !IG_labNodes_len_cardinal.
    assumption.
Qed.



Theorem _IG_match_decreases_IG_noNodes : forall (A B : Type) (n : Node) (c : Context A B) (ig rest : IG A B),
    IG_match n ig = (Some c, rest) -> IG_noNodes rest < IG_noNodes ig.
Proof.
    intros.
    apply _IG_match_minusOnes_IGnoNodes in H. lia.
Qed.


Theorem _IG_matchAny_decreases_IG_noNodes : forall (A B : Type) (c : Context A B) (ig rest : IG A B),
    IG_matchAny ig = (Some c, rest) -> IG_noNodes rest < IG_noNodes ig.
Proof.
    intros. unfold IG_matchAny in H. destruct (IG_labNodes ig) eqn:labNodes.
    - inversion H.
    - apply _IG_match_decreases_IG_noNodes in H. assumption.
Qed.




(* TODO: This is another approach of proving the same. Check it out perhaps. So far nothing depends on it *)

Require Import Coq.Sorting.Permutation.

Lemma _lists_diff_by_one : forall (A : Type) (l l' : list A) (x diff : A),
    Permutation l (diff :: l') -> length l = S (length l').
Proof.
    intros. apply Permutation_length in H. simpl in H. assumption.
Qed.

Lemma IG_match_labNodes_permuation : forall (A B : Type) (n : Node) (c : Context A B) (ig rest : IG A B),
    IG_match n ig = (Some c, rest) -> let '(_, node, label, _) := c in Permutation (IG_labNodes ig) ((node, label) :: IG_labNodes rest).
Proof.
Admitted. 


Theorem _IG_match_decreases_nodeAmount_permutation : forall (A B : Type) (n : Node) (c : Context A B) (ig rest : IG A B),
    IG_match n ig = (Some c, rest) -> IG_noNodes rest < IG_noNodes ig.
Proof.
    intros. destruct c as [[[froms node] label] tos]. apply IG_match_returns_node in H as s. subst.
    assert (NatMap.cardinal ig = S (NatMap.cardinal rest)). {
        rewrite <- !IG_labNodes_len_cardinal.
        apply IG_match_labNodes_permuation in H.
        apply _lists_diff_by_one in H.
        - assumption.
        - apply (node, label).
    }
    rewrite !IG_labNodes_len_cardinal. 
    lia.
Qed.