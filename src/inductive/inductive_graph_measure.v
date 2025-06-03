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



Lemma IG_labNodes_len_cardinal : forall (A B : Type) (ig : IG A B),
    NatMap.cardinal ig = IG_noNodes ig.
Proof.
    intros. unfold IG_noNodes. unfold IG_labNodes. rewrite map_length.
    rewrite NatMap.cardinal_1. reflexivity. 
Qed.

Lemma IG_match_returns_node : forall (A B : Type) (query hit : Node) (ig i : IG A B) (froms tos : Adj B) (l : A),
    IG_match query ig = (Some (froms, hit, l, tos), i) -> query = hit.
Proof.
    intros. unfold IG_match in H. destruct (NatMap.find query ig).
    - unfold _cleanSplit in H. destruct c as [[fromss label] toss]. inversion H. reflexivity. 
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
  - 

  assert (NatMap.Equal ig (NatMap.add node c ig)). { 
      apply MFacts.find_mapsto_iff in split.

    apply MFacts.Equal_mapsto_iff.
    split; intros.
    - apply MFacts.add_mapsto_iff.
       bdestruct (node =? k).
      + subst. left. split.
      -- reflexivity.
      -- apply MFacts.find_mapsto_iff in split. apply MFacts.find_mapsto_iff in H. rewrite H in split. inversion split. reflexivity.
      + right. split.
      -- assumption.
      -- assumption.
    - apply MFacts.add_mapsto_iff in H. destruct H.
      + destruct H. subst. assumption.
      + destruct H. assumption.
  }
  rewrite H at 2.
  apply NatMap_add_value_does_not_matter_for_cardinality.
  - reflexivity.
Qed.



Lemma _IG_updAdj_does_not_change_cardinality : forall {A B : Type} (adj : Adj B) (f : B -> Context' A B -> Context' A B) (ig : IG A B), 
    NatMap.cardinal (_updAdj adj f ig) = NatMap.cardinal ig.
Proof.
  intros.
  unfold _updAdj.
  induction adj.
  - simpl. reflexivity.
  - simpl. rewrite <- IHadj.
    pose proof (@_IG_updateEntry_does_not_change_cardinality A B).
    destruct a.
    rewrite H. reflexivity.
Qed.





Theorem _IG_match_decreases_IG_noNodes : forall (A B : Type) (n : Node) (c : Context A B) (ig rest : IG A B),
    IG_match n ig = (Some c, rest) -> IG_noNodes rest < IG_noNodes ig.
Proof.
    intros. destruct c as [[[froms node] label] tos]. apply IG_match_returns_node in H as s. subst.
    assert (NatMap.cardinal ig = S (NatMap.cardinal rest)). {

        unfold IG_match in H.
        destruct (NatMap.find node ig) eqn:split.
        - destruct (_cleanSplit node c (NatMap.remove node ig)) eqn:split0.
            inversion H. subst.
            unfold _cleanSplit in split0.
            destruct c as [[fromss labell] toss].
            inversion split0.
            clear split0 H1.
            


            rewrite _IG_updAdj_does_not_change_cardinality.
            rewrite _IG_updAdj_does_not_change_cardinality.
            apply symmetry.
            apply NatMap_map_find_some_remove_lowers_cardinality.

            exists (fromss, labell, toss).
            apply split.
        - inversion H.
    }
    rewrite <- !IG_labNodes_len_cardinal.
    lia.
Qed.



Theorem _IG_matchAny_decreases_IG_noNodes : forall (A B : Type) (c : Context A B) (ig rest : IG A B),
    IG_matchAny ig = (Some c, rest) -> IG_noNodes rest < IG_noNodes ig.
Proof.
    intros. unfold IG_matchAny in H. destruct (IG_labNodes ig) eqn:labNodes.
    - inversion H.
    - apply _IG_match_decreases_IG_noNodes in H. assumption.
Qed.