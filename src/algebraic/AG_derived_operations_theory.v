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
Require Import GraphVerification.src.algebraic.AG_algebra_theory.

(** Stating and proving Lemmas and Theorems about functions which are
    defined using the primitive operations of an AG.
    Notably: Relating AG_transpose to RG_transpose and characterizing the result of AG_BFS
*)



(* AG_transpose relates to RG_transpose *)
Theorem AG_transpose_relates : forall (ag : AG nat),
    AG_to_RG (AG_transpose ag) ==R RG_transpose (AG_to_RG ag). 
Proof.
    intros. induction ag; simpl; firstorder.
Qed.
    





(** Start Proving properties on AG_BFS *)


(* Lemma building towards AG_BFS_no_duplicates *)

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








(* Here are attempts at specifying which elements are in BFS and in which order *)


Lemma AG_nodeAmount_empty :
    AG_nodeAmount AG_empty = 0.
Proof.
    unfold AG_nodeAmount. reflexivity.
Qed.

Lemma NatSet_emptyElements : forall (nodes : list Node),
    NatSet.elements (NatSet.inter (NatSet_fromList nodes) NatSet.empty) = [].
Proof.
    intros.
    apply SProps.MP.elements_Empty. apply SProps.MP.empty_inter_2. apply NatSet.empty_spec.
Qed.


Require Import Relation_Operators.

Lemma if_same_result : forall (A : Type) (a : A) (b : bool),
    (if b then a else a) = a.
Proof.
    intros. destruct b. reflexivity. reflexivity.
Qed.

Require Import GraphVerification.src.util.util.
Require Import Arith.

(* About what is included, can also add that every node that has a path is i the result *)
Theorem AG_BFS_path : forall (nodes : list nat) (ag : AG nat) x,
    In x (AG_BFS nodes ag)
        -> In x nodes \/ exists y, In y nodes /\ RG_existsPath y x (AG_to_RG ag). 
Proof.
    intros. induction ag.
    - exfalso. unfold AG_BFS in H. simpl in H. rewrite NatSet_emptyElements in H. destruct (NatSet.equal (NatSet.inter (NatSet_fromList nodes) NatSet.empty)
(NatSet.union (NatSet.inter (NatSet_fromList nodes) NatSet.empty) NatSet.empty)).
        ++ simpl in H. inversion H.
        ++ simpl in H. inversion H.
    - left. 
        unfold AG_BFS in H.
        apply _consolidation_fold_right_preserves_nodes in H.
        destruct H. destruct H.
        simpl in H. destruct H.
        + destruct (existsb (Nat.eqb a) nodes) eqn:has.
            -- admit.
            -- exfalso. admit. 
        + rewrite if_same_result in H.
            destruct (NatSet.equal (NatSet.inter (NatSet_fromList nodes) (NatSet.singleton a)) (NatSet.union (NatSet.inter (NatSet_fromList nodes) (NatSet.singleton a)) NatSet.empty)).
            -- inversion H.
            -- simpl in *. destruct H. 
                ++ subst. apply SProps.MP.FM.empty_iff in H0. inversion H0.
                ++ inversion H.
    - unfold AG_BFS in H.
        apply _consolidation_fold_right_preserves_nodes in H.
        destruct H. destruct H.
        simpl in H. destruct H.

Admitted.





Theorem AG_BFS_path' : forall (nodes : list nat) (ag : AG nat) x,
    In x (AG_BFS nodes ag)
        -> In x nodes \/ exists y, In y nodes /\ RG_existsPath y x (AG_to_RG ag). 
Proof.
    intros.  
    unfold AG_BFS in H.
    apply _consolidation_fold_right_preserves_nodes in H.
    destruct H. destruct H.
    induction ag.
    - admit.
    - admit.
    - simpl in H. destruct H.
        + left. admit.
        + destruct (NatSet.equal (NatSet.inter (NatSet_fromList nodes) (NatSet.union (AG_nodeSet ag1) (AG_nodeSet ag2)))
(NatSet.union (NatSet.inter (NatSet_fromList nodes) (NatSet.union (AG_nodeSet ag1) (AG_nodeSet ag2)))
(NatSet.union (_singleStep (NatSet.inter (NatSet_fromList nodes) (NatSet.union (AG_nodeSet ag1) (AG_nodeSet ag2))) ag1)
(_singleStep (NatSet.inter (NatSet_fromList nodes) (NatSet.union (AG_nodeSet ag1) (AG_nodeSet ag2))) ag2)))).
            -- inversion H.
            -- unfold RG_existsPath.
                 (* Now that I think of how RG_existsPath would even be split up, I don't really know how this could be continued..... hmmm. There is the problem, that if one does a zig zag from ag1 to ag2. combining the two IH is not really enough, right? *)
            
            
            

Admitted.







(* Testing BFS oder functions on a specific examples *)

(* Testing that two specific nodes indeed have the same distance to some starting set *)
Lemma sameDistance_caller_test1 : sameDistance (fun x => x = 1) 2 3 (AG_to_RG (1 *** 2 +++ 1 *** 3)).
Proof.
    unfold sameDistance.
    apply bothOneStep.
    apply bothInStart.
    - simpl. unfold RG_reachableInOneStep. exists 1, tt. firstorder.
    - simpl. unfold RG_reachableInOneStep. exists 1, tt. firstorder.
Qed.


    
Lemma distanceSecondOneLower_test1 : distanceSecondOneLower (fun x => x = 1) 4 2 (AG_to_RG (1 *** 2 +++ 1 *** 3 +++ 3 *** 4)).
Proof.
    unfold distanceSecondOneLower.
    apply bothOneStep.
    apply bothInStart.
    - simpl. unfold RG_reachableInOneStep. exists 3, tt. firstorder. exists 1, tt. firstorder.
    - simpl. unfold RG_reachableInOneStep. exists 1, tt. firstorder.
Qed.



(* Testing that BFS_Order holds for a specific example *)
Lemma revBFS_Order_test1 : BFS_Order [1] (AG_BFS [1] (1 *** 2 +++ 1 *** 3 +++ 3 *** 4)) (AG_to_RG (1 *** 2 +++ 1 *** 3 +++ 3 *** 4)).
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



(* Actual specification about the order of nodes from BFS *)
Theorem AG_BFS_order : forall (nodes : list nat) (ag : AG nat),
    BFS_Order nodes (AG_BFS nodes ag) (AG_to_RG ag).
Proof.
    intros.
Admitted.






























(* Todo: clean this up *)


(* Showing some experimental properties about AGs *)


(* Initially functions from the paper *)

(* Definition AG_edge {A : Type} (a1 a2 : A) : AG A :=
    (AG_vertex a1) *** (AG_vertex a2). *)

Lemma AG_edge_relates : forall (A : Type) (a1 a2 : A),
    RG_addEdge a1 a2 tt RG_empty ==R AG_to_RG (AG_edge a1 a2).
Proof.
    intros. unfold AG_edge. unfold AG_to_RG. firstorder.
    - subst. firstorder.
    - destruct b. firstorder.
Qed.


Lemma AG_vertices_relates : forall (A : Type) (l : list A),
    fold_right RG_addNode RG_empty l ==R AG_to_RG (AG_vertices l).
Proof.
    intros. induction l.
    - firstorder.
    - unfold AG_vertices in *. simpl in *. firstorder.
Qed.

Lemma AG_edges_relates : forall (A : Type) (l : list (A * A)),
    fold_right (fun '(a1, a2) acc => RG_addEdge a1 a2 tt acc) RG_empty l ==R AG_to_RG (AG_edges l).
Proof.
    intros. induction l.
    - firstorder.
    - unfold AG_edges in *. simpl in *.
    (* firstorder. *)
Admitted.

(* Lemma AG_clique_relates : forall (A : Type) (l : list A),
    fold_right RG_addNode RG_empty l ==R AG_to_RG (AG_clique l).
Proof.
    intros. induction l.
    - firstorder.
    - unfold AG_clique in *. simpl in *. firstorder. *)


(* Lemma AG_makeGraph_relates : forall (A : Type) (vs : list A) (es : list (A * A)),
    RG_makeGraph vs es ==R AG_to_RG (AG_makeGraph vs es). *)



(* Lemma AG_path_relates : forall (A : Type) (l : list A),
    RG_path l ==R AG_to_RG (AG_path l). *)


(* Lemma AG_circuit_relates : forall (A : Type) (l : list A),
    RG_circuit l ==R AG_to_RG (AG_circuit l). *)

(* Lemma AG_star_relates : forall (A : Type) (x : A) (l : list A),
    RG_star x l ==R AG_to_RG (AG_star x l). *)

Definition RG_gmap {A A' B : Type} (f: A -> A') (rg : RG A B) : RG A' B.
Proof.
    refine {|
        RG_nodes := fun a => exists n, rg.(RG_nodes) n /\ f n = a;
        RG_edges := fun a1 a2 l => exists n1 n2, rg.(RG_edges) n1 n2 l /\ f n1 = a1 /\ f n2 = a2;
        RG_valid := _
    |}.
    RG_valid_prover_with rg.
    - unfold _valid_cond in H. apply H in H0. firstorder.
    - unfold _valid_cond in H. apply H in H0. firstorder.
Defined.

Lemma RG_gmap_relates : forall (A A' : Type) (f: A -> A') (ag : AG A),
    RG_gmap f (AG_to_RG ag) ==R AG_to_RG (AG_gmap f ag).
Proof.
    intros. induction ag.
    - compute. firstorder.
    - compute. firstorder. congruence.
    - simpl. assert (AG_to_RG (AG_gmap f ag1) = RG_gmap f (AG_to_RG ag1)). {
            admit.
        }
        assert (AG_to_RG (AG_gmap f ag2) = RG_gmap f (AG_to_RG ag2)). {
            admit.
        }
        rewrite H.
        rewrite H0.
        clear.
        firstorder.
    - simpl. assert (AG_to_RG (AG_gmap f ag1) = RG_gmap f (AG_to_RG ag1)). {
            admit.
        }
        assert (AG_to_RG (AG_gmap f ag2) = RG_gmap f (AG_to_RG ag2)). {
            admit.
        }
        rewrite H.
        rewrite H0.
        clear.
        firstorder.
Admitted.

(* Lemma AG_mergeVertices_relates : forall (A : Type) (f : A -> bool) (v : A) (ag : AG A),
    RG_mergeVertices f v (AG_to_RG ag) ==R AG_to_RG (AG_mergeVertices f v ag). *)

Lemma AG_toList_relates : forall (A : Type) (ag : AG A),
    forall x, (AG_to_RG ag).(RG_nodes) x <-> In x (AG_toList ag).
Proof.
    intros. induction ag.
    - simpl. firstorder.
    - simpl. firstorder.
    - simpl. rewrite IHag1. rewrite IHag2. rewrite in_app_iff. clear. firstorder.
    - simpl. rewrite IHag1. rewrite IHag2. rewrite in_app_iff. clear. firstorder.
Qed.


Lemma AG_removeVertex_relates : forall (x : nat) (ag : AG nat),
    RG_removeNode x (AG_to_RG ag) ==R AG_to_RG (AG_removeVertex x ag).
Proof.
    intros. induction ag.
    - firstorder.
    - unfold AG_removeVertex. unfold AG_induce. simpl. bdestruct (x =? a).
        + subst. simpl. firstorder.
        + simpl. firstorder. compute in H0. subst. assumption.
    - simpl.
        assert (AG_to_RG (AG_removeVertex x ag1) = RG_removeNode x (AG_to_RG ag1)). {
            admit.
        }
        assert (AG_to_RG (AG_removeVertex x ag2) = RG_removeNode x (AG_to_RG ag2)). {
            admit.
        }
Admitted. 



Lemma AG_removeEdge_relates : forall (x y : nat) (ag : AG nat),
    RG_removeEdge x y tt (AG_to_RG ag) ==R AG_to_RG (AG_removeEdge x y ag).
Proof.
    intros. induction ag.
    - firstorder.
    - firstorder.
    - simpl.
        assert (AG_to_RG (AG_removeEdge x y ag1) = RG_removeEdge x y tt (AG_to_RG ag1)). {
            admit.
        }
        assert (AG_to_RG (AG_removeEdge x y ag2) = RG_removeEdge x y tt (AG_to_RG ag2)). {
            admit.
        }
        rewrite H.
        rewrite H0.
        clear.
        firstorder.
    - simpl. assert (forall x ag, RG_removeNode x (AG_to_RG ag) = AG_to_RG (AG_removeVertex x ag)). {
            admit.
    }
    rewrite <- !H. clear. unfold RG_equiv. split; intros.
        + simpl. firstorder.
        + simpl. destruct b. firstorder.
Admitted.



