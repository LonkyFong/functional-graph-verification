

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




(* This proof is adapted from the link below. It blows my mind, that this is not in stdlib *)
(* https://github.com/rocq-prover/stdlib/blob/master/theories/FSets/FMapFacts.v *)
(* TODO: this kills coq, omg *)
Lemma cardinal_Add_In:
    forall (A : Type) (m m' : NatMap.t A) x e, NatMap.In x m -> MProps.Add x e m m' -> NatMap.cardinal m' = NatMap.cardinal m.
  Proof.
  assert (forall {A : Type} (k : Node) (e : A ) m, NatMap.MapsTo k e m -> MProps.Add k e (NatMap.remove k m) m) as remove_In_Add.
  { intros. unfold MProps.Add.
    intros.
    rewrite MFacts.add_o.
    destruct (MFacts.eq_dec k y).
    - apply NatMap.find_1. rewrite <- MFacts.MapsTo_m; [exact H|assumption|reflexivity|reflexivity].
    - rewrite MFacts.remove_neq_o by assumption. reflexivity.
  }
  intros.
  assert (NatMap.Equal (NatMap.remove x m) (NatMap.remove x m')).
  { intros y. rewrite 2!MFacts.remove_o.
    destruct (MFacts.eq_dec x y).
    - reflexivity.
    - unfold MProps.Add in H0. rewrite H0.
      rewrite MFacts.add_neq_o by assumption. reflexivity.
  }
  Admitted.
  (* apply MProps.Equal_cardinal in H1.
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
  Qed. *)



Lemma _add_value_does_not_matter_for_cardinality : forall {A : Type} (node : Node) (c c' : A) (m : NatMap.t A),
  NatMap.cardinal (NatMap.add node c m) = NatMap.cardinal (NatMap.add node c' m).
Proof.
  intros.
  pose proof cardinal_Add_In.
  apply (H _ _ _ node c).
  - apply MFacts.add_in_iff. left. reflexivity.
  - unfold MProps.Add. intros. rewrite MFacts.add_o. rewrite MFacts.add_o. rewrite MFacts.add_o. destruct (MProps.F.eq_dec node y).
    + reflexivity.
    + reflexivity.
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
  apply _add_value_does_not_matter_for_cardinality.
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


Lemma _map_find_some_remove_lowers_cardinality : forall {A : Type} (key : Node) (map : NatMap.t A),
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






