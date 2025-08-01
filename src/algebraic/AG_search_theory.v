Require Import Setoid Morphisms.
Require Import Ensembles.

Require Import List.
Import ListNotations.
Require Import Sorting.Permutation.

Require Import GraphVerification.src.util.NatSet.
Require Import GraphVerification.src.util.util.

Require Import GraphVerification.src.relational.RG.
Require Import GraphVerification.src.relational.RG_theory.

Require Import GraphVerification.src.algebraic.AG.
Require Import GraphVerification.src.algebraic.AG_to_RG.


(** Stating and proving Lemmas and Theorems about breadth-first search on AGs *)


(* Lemmas building towards AG_BFS_no_duplicates *)

Lemma NatList_filterOutOf_makes_subset : forall (s : NatSet.t) (l : list nat),
    incl (NatList_filterOutOf s l) l.
Proof.
    unfold incl. intros. unfold NatList_filterOutOf in H. apply filter_In in H. firstorder.
Qed.


Lemma NatList_filterOutOf_splits_In : forall (s : NatSet.t) (l : list nat) x,
    In x l -> In x (NatSet.elements s) \/ In x (NatList_filterOutOf s l).
Proof.
    intros. induction l; simpl in *.
    - destruct H.
    - destruct H.
        + subst. destruct (negb (NatSet.mem x s)) eqn:mem.
            -- right. firstorder.
            -- left. apply Bool.negb_false_iff in mem. apply NatSet.mem_spec in mem. apply NatSet_In_is_In_elements. auto.
        + specialize (IHl H). destruct IHl.
            -- left.  assumption.
            -- right. simpl. destruct (negb (NatSet.mem a s)); firstorder.
Qed.


Lemma NatList_filterOutOf_disjoint : forall (s : NatSet.t) (l : list nat),
    disjoint (NatSet.elements s) (NatList_filterOutOf s l).
Proof.
    unfold disjoint. intros. destruct H.
    unfold NatList_filterOutOf in H0.

    apply NatSet_In_is_In_elements in H.

    induction l.
    - firstorder.
    - simpl in H0. apply IHl. destruct (negb (NatSet.mem a0 s)) eqn:isin.
        + firstorder. subst. apply Bool.negb_true_iff in isin. apply NatSet.mem_spec in H. rewrite H in isin. discriminate isin.
        + assumption.
Qed.

Lemma NoDup_fold_right_filterOutOf : forall (l : list (NatSet.t)),
    NoDup (fold_right (fun (next : NatSet.t) (acc : list nat) => NatSet.elements next ++ NatList_filterOutOf next acc) nil l).
Proof.
    intros. induction l.
    - simpl. apply NoDup_nil.
    - simpl. apply nodup_app. split.
        + apply NatSet_NoDup_elements.
        + split.
            -- apply NoDup_filter. assumption.
            -- apply NatList_filterOutOf_disjoint.
Qed.

Theorem AG_BFS_no_duplicates : forall (nodes : list nat) (ag : AG nat),
    NoDup (AG_BFS nodes ag).
Proof.
    intros.
    unfold AG_BFS.
    apply NoDup_fold_right_filterOutOf.
Qed.




(* Lemmas building towards AG_BFS_returns_only_nodes *)

Lemma _consolidation_fold_right_preserves_nodes : forall (l : list (NatSet.t)) y,
    (exists x, In x l /\ NatSet.In y x) <-> (In y (fold_right (fun next acc => NatSet.elements next ++ NatList_filterOutOf next acc) nil l)) .
Proof. 
    intros. induction l; simpl.
    - firstorder.
    - split; intros.
        + destruct H. simpl in H. destruct H. destruct H.
            -- subst. simpl. apply in_or_app. left. apply NatSet_In_is_In_elements. auto.
            -- simpl. apply in_or_app. apply NatList_filterOutOf_splits_In. apply IHl. firstorder.
        + apply in_app_or in H. destruct H.
            -- exists a. rewrite NatSet_In_is_In_elements. auto.
            -- destruct IHl. apply NatList_filterOutOf_makes_subset in H. apply H1 in H. firstorder.
Qed.



Lemma In_AG_nodeSet_is_In_RG : forall (ag : AG nat),
    forall x, NatSet.In x (AG_nodeSet ag) <-> (AG_to_RG ag).(RG_nodes) x.
Proof.
    intros. induction ag.
    - simpl. apply SProps.MP.FM.empty_iff.
    - simpl. rewrite NatSet.singleton_spec. firstorder.
    (* firstorder works, but is just too slow here *)
    - simpl. rewrite NatSet.union_spec. rewrite IHag1. rewrite IHag2. reflexivity.
    - simpl. rewrite NatSet.union_spec. rewrite IHag1. rewrite IHag2. reflexivity.
Qed.


Lemma _singleStep_returns_only_nodes : forall (from : NatSet.t) (ag : AG nat),
    forall x, NatSet.In x (_singleStep from ag) -> (AG_to_RG ag).(RG_nodes) x.
Proof.
    intros. induction ag; simpl in *.
    - apply NatSet_In_is_In_elements in H. simpl in H. destruct H.
    - apply NatSet_In_is_In_elements in H. simpl in H. destruct H.
    - apply NatSet.union_spec in H. destruct H. 
        + left. apply IHag1. assumption.
        + right. apply IHag2. assumption.
     
    - apply NatSet.union_spec in H. destruct H. 
        + apply NatSet.union_spec in H. destruct H.
            -- left. apply IHag1. assumption.
            -- right. apply IHag2. assumption.
        + destruct (NatSet.is_empty (NatSet.inter (AG_nodeSet ag1) from)) eqn:split.
            -- apply NatSet_In_is_In_elements in H. simpl in H. destruct H.
            -- right. apply In_AG_nodeSet_is_In_RG. assumption.
Qed.


Lemma _upToNStepsCap_rec_returns_only_nodes : forall (from s: NatSet.t) (ag : AG nat) (n : nat),
    forall x y, NatSet.Subset from (AG_nodeSet ag) ->
    In x (_upToNStepsCap_rec from s ag n) -> NatSet.In y x -> (AG_to_RG ag).(RG_nodes) y.
Proof.
    intros. generalize dependent from. generalize dependent s. induction n; intros; simpl in *.
    - contradiction.
    - destruct H0.
        + subst. apply In_AG_nodeSet_is_In_RG. unfold NatSet.Subset in H. apply H. assumption.
        + destruct (NatSet.equal s (NatSet.union s (_singleStep from ag))).  
            -- simpl in H0. contradiction.
            -- specialize (IHn (NatSet.union s (_singleStep from ag)) (_singleStep from ag)).
               apply IHn.
               ++ unfold NatSet.Subset. intros.
                    apply _singleStep_returns_only_nodes in H2. apply In_AG_nodeSet_is_In_RG. assumption.
               ++ assumption.
Qed.


Lemma _upToNStepsCap_returns_only_nodes : forall (from : NatSet.t) (ag : AG nat) (n : nat),
    forall x y, In x (_upToNStepsCap from ag n) -> NatSet.In y x -> (AG_to_RG ag).(RG_nodes) y.
Proof.
    intros.
    pose proof _upToNStepsCap_rec_returns_only_nodes.
    specialize (H1 (NatSet.inter from (AG_nodeSet ag)) (NatSet.inter from (AG_nodeSet ag)) ag (S n) x).
    apply H1.
    - unfold NatSet.Subset. intros. apply NatSet.inter_spec in H2. destruct H2. assumption.
    - unfold _upToNStepsCap in H. apply H.
    - assumption.
Qed.


Theorem AG_BFS_returns_only_nodes : forall (nodes : list nat) (ag : AG nat),
    forall x, In x (AG_BFS nodes ag) -> (AG_to_RG ag).(RG_nodes) x. 
Proof.
    intros. unfold AG_BFS in H. apply _consolidation_fold_right_preserves_nodes in H.
    destruct H. destruct H.
    apply (_upToNStepsCap_returns_only_nodes _ _ _ _ x) in H; auto.
Qed.




(** This section becomes a little experimental:
    While we did develop and attempt for a Rocq specification of BFS, we could not show
    it applies in all cases. Nevertheless, we could show it holds for a specific "testcase".
    One would additionally need to show that the search is complete, ie.,
    all reachable elements from the graph are included. *)


Lemma BFS_Order_test :
    BFS_Order [1] (AG_BFS [1] (1 *** 2 +++ 1 *** 3 +++ 3 *** 4)) (AG_to_RG (1 *** 2 +++ 1 *** 3 +++ 3 *** 4)).
Proof.
    unfold BFS_Order. simpl.
    apply revBFS_Order_next.
    - unfold distanceSecondOneLower. apply bothOneStep. apply bothInStart.
        + unfold RG_reachableInOneStep. simpl. exists 3, tt. firstorder. exists 1, tt. firstorder.
            apply NatSet.singleton_spec. reflexivity.
        + unfold RG_reachableInOneStep. simpl. exists 1, tt. firstorder.
            apply NatSet.singleton_spec. reflexivity.

    - apply revBFS_Order_same.
        + unfold sameDistance. apply bothOneStep. apply bothInStart.
            -- unfold RG_reachableInOneStep. simpl. exists 1, tt. firstorder.
                apply NatSet.singleton_spec. reflexivity.
            -- unfold RG_reachableInOneStep. simpl. exists 1, tt. firstorder.
                apply NatSet.singleton_spec. reflexivity.
        + apply revBFS_Order_next.
            -- unfold distanceSecondOneLower. apply bothInStart.
                ++ unfold RG_reachableInOneStep. simpl. exists 1, tt. firstorder.
                    apply NatSet.singleton_spec. reflexivity.
                ++ apply NatSet.singleton_spec. reflexivity.
            -- apply revBFS_Order_start. apply perm_skip. apply perm_nil.
Qed.
