Require Import Setoid Morphisms.
Require Import Ensembles.

Require Import List.
Import ListNotations.
Require Import Sorting.Permutation.

Require Import GraphVerification.src.util.NatSet.

Require Import GraphVerification.src.RG.
Require Import GraphVerification.src.RG_theory.

Require Import GraphVerification.src.algebraic.AG.
Require Import GraphVerification.src.algebraic.AG_to_RG.

(* Stating and proving Lemmas and Theorems about AGs *)

(* This is used to verify that the axioms on the algebra of AGs are consistent
with the interpretation of the expressions in terms of RGs *)
Ltac AG_axiom_proof_automation_via_RG :=
    unfold AG_equiv; simpl; firstorder.

(* These are the "8 axioms" originally proposed by functional graphs with class *)

(* +++ is commutative and associative *)
Theorem AG_overlay_Commutative {A : Type} : forall (ag1 ag2 : AG A), ag1 +++ ag2 A== ag2 +++ ag1.
Proof.
    AG_axiom_proof_automation_via_RG.
Qed.

Theorem AG_overlay_Associative {A : Type} : forall (ag1 ag2 ag3 : AG A), ag1 +++ (ag2 +++ ag3) A== (ag1 +++ ag2) +++ ag3.
Proof.
    AG_axiom_proof_automation_via_RG.
Qed.

(* (G, ***, e) is a monoid *)
Theorem AG_empty_connect_L_Identity {A : Type} : forall (ag : AG A), AG_empty *** ag A== ag.
Proof.
    AG_axiom_proof_automation_via_RG.
Qed.

Theorem AG_empty_connect_R_Identity {A : Type} : forall (ag : AG A), ag *** AG_empty A== ag.
Proof.
    AG_axiom_proof_automation_via_RG.
Qed.

Theorem AG_connect_Associative {A : Type} : forall (ag1 ag2 ag3 : AG A), ag1 *** (ag2 *** ag3) A== (ag1 *** ag2) *** ag3.
Proof.
    AG_axiom_proof_automation_via_RG.
Qed.

(* *** distributes over +++ *)
Theorem AG_connect_overlay_L_Distributes {A : Type} : forall (ag1 ag2 ag3 : AG A), ag1 *** (ag2 +++ ag3) A== ag1 *** ag2 +++ ag1 *** ag3.
Proof.
    AG_axiom_proof_automation_via_RG.
Qed.

Theorem AG_connect_overlay_R_Distributes {A : Type} : forall (ag1 ag2 ag3 : AG A), (ag1 +++ ag2) *** ag3 A== ag1 *** ag3 +++ ag2 *** ag3.
Proof.
    AG_axiom_proof_automation_via_RG.
Qed.

(* Decomposition *)
Theorem AG_connect_Decomposition {A : Type} : forall (ag1 ag2 ag3 : AG A), ag1 *** ag2 *** ag3 A== ag1 *** ag2 +++ ag1 *** ag3 +++ ag2 *** ag3.
Proof.
    AG_axiom_proof_automation_via_RG.
Qed.




(* Section to make rewrite work with A== of overlays and connects *)
(* This proof is based on R== being an equivalence relation *)
Instance AG_Equivalence {A : Type} : Equivalence (@AG_equiv A).
Proof.
    G_derived_equivalence_prover A unit (@AG_to_RG A).
Qed.

Ltac Proper_proof_automation := split; simpl in *; firstorder.

Instance Proper_overlay {A : Type} : Proper ((@AG_equiv A) ==> AG_equiv ==> AG_equiv) AG_overlay.
Proof.
    Proper_proof_automation.
Qed.

Instance Proper_connect {A : Type} : Proper ((@AG_equiv A) ==> AG_equiv ==> AG_equiv) AG_connect.
Proof.
    Proper_proof_automation.
Qed.




(* The following theorems are provable using the same automation as the 8 axioms,
but this section aims to demonstrate their utility, by using only them.
This has already been done in the Agda formalization by Andrey Mokhov *)

(* This is a helper for multiple theorems *)
Lemma _overlay_preidempotence {A : Type}: forall (ag : AG A), ag +++ ag +++ AG_empty A== ag.
Proof.
    intros.
    pose proof (AG_connect_Decomposition ag AG_empty AG_empty).

    rewrite AG_empty_connect_R_Identity in H.
    rewrite AG_empty_connect_R_Identity in H.
    rewrite <- H.

    reflexivity.
Qed.


(* Identity of + *)
Theorem AG_empty_overlay_R_Identity {A : Type}: forall (g : AG A), g +++ AG_empty A== g.
Proof.
    intros.
    rewrite <- _overlay_preidempotence.

    rewrite <- AG_overlay_Associative.
    rewrite (AG_overlay_Associative AG_empty (g +++ AG_empty)). 
    rewrite (AG_overlay_Commutative AG_empty (g +++ AG_empty)).
    rewrite <- AG_overlay_Associative.
    rewrite <- AG_overlay_Associative.

    rewrite _overlay_preidempotence.
    rewrite _overlay_preidempotence.
    reflexivity.
Qed.


(* Idempotence of + *)
Theorem AG_overlay_Idempotence {A : Type}: forall (ag : AG A), ag +++ ag A== ag.
Proof.
    intros.
    pose proof _overlay_preidempotence ag.
    rewrite AG_empty_overlay_R_Identity in H.
    assumption.
Qed.


(* Absorption *)
Theorem AG_Absorption {A : Type}: forall (ag1 ag2 : AG A), ag1 *** ag2 +++ ag1 +++ ag2 A== ag1 *** ag2.
Proof.
    intros. pose proof AG_connect_Decomposition ag1 ag2 AG_empty.
    rewrite (AG_connect_Associative) in H.
    rewrite AG_empty_connect_R_Identity in H.
    rewrite AG_empty_connect_R_Identity in H.
    rewrite AG_empty_connect_R_Identity in H.
    symmetry in H.
    assumption.
Qed.


(* Saturation *)
Theorem AG_Saturation {A : Type}: forall (ag : AG A), ag *** ag *** ag A== ag *** ag.
Proof.
    intros.
    rewrite AG_connect_Decomposition.

    rewrite AG_overlay_Idempotence.
    rewrite AG_overlay_Idempotence.
    reflexivity.
Qed.




(* AG_transpose relates to RG_transpose *)
Theorem AG_transpose_is_RG : forall (ag : AG nat),
    AG_to_RG (AG_transpose ag) R== RG_transpose (AG_to_RG ag). 
Proof.
    intros. induction ag; simpl; firstorder.
Qed.
    




(* Start Proving properties on AG_BFS *)


(* Some more basics about NoDup and disjointness: *)
Definition disjoint {A : Type} (l1 l2 : list A) :=
  forall a, In a l1 /\ In a l2 -> False.  


Lemma nodup_app: forall (A: Type) (l1 l2: list A),
  NoDup (l1 ++ l2) <->
  NoDup l1 /\ NoDup l2 /\ disjoint l1 l2.
Proof.
    intros. unfold disjoint. induction l1; simpl.
    - firstorder. apply NoDup_nil.
    - split; intros.
        + inversion H. apply IHl1 in H3. destruct H3 as [H30 [H31 H32]].
            split.
            -- apply NoDup_cons.
                ++ unfold not. intros. unfold not in H2. apply H2. apply in_or_app. firstorder.
                ++ assumption.
            -- split.
                ++ assumption.
                ++ subst. intros. unfold not in H2. apply H2.
                    simpl in *. destruct H0. apply in_or_app. destruct H0.
                    --- subst. auto.
                    --- firstorder.
        + destruct H. destruct H0. inversion H. apply NoDup_cons.
            -- subst. unfold not. intros.
                apply in_app_or in H2. apply (H1 a). firstorder.
            -- apply IHl1. firstorder.
Qed.



(* Some Helper Lemmas on NatSets and their elements *)
Lemma NatSet_In_is_In_elements : forall (x : Node) (s : NatSet.t),
    NatSet.In x s <-> In x (NatSet.elements s).
Proof.
    intros. rewrite <- NatSet.elements_spec1. rewrite SetoidList.InA_alt. firstorder. subst. auto.
Qed.

Lemma NoDup_NatSet_elements : forall (s : NatSet.t),
    NoDup (NatSet.elements s).
Proof.
    intros. pose proof (NatSet.elements_spec2w s). induction (NatSet.elements s).
    - apply NoDup_nil.
    - inversion H. apply NoDup_cons.
        + unfold not in *. intros. apply H2. apply SetoidList.InA_alt. exists a. auto.
        + apply IHl. assumption.
Qed.



(* Helper Lemmas on NatList_filterOutOf: *)
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
        + apply NoDup_NatSet_elements.
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








(* About the order of BFS *)
Inductive sameDistance_rec {A B : Type} (rg : RG A B) : Ensemble A -> A -> Ensemble A -> A -> Prop :=
    | bothInStart (start1 start2 : Ensemble A) : forall (a1 a2 : A), start1 a1 -> start2 a2 -> sameDistance_rec rg start1 a1 start2 a2
    | bothOneStep (start1 start2 : Ensemble A) : forall (a1 a2 : A),
        sameDistance_rec rg (fun x => RG_reachableInOneStep start1 x rg) a1 (fun x => RG_reachableInOneStep start2 x rg) a2
        -> sameDistance_rec rg start1 a1 start2 a2. 

Definition sameDistance {A B : Type} (start : Ensemble A) (a1 a2 : A) (rg : RG A B) : Prop :=
    sameDistance_rec rg start a1 start a2.

(* Testing that two specific nodes indeed have the same distance to some starting set *)
Lemma sameDistance_caller_test1 : sameDistance (fun x => x = 1) 2 3 (AG_to_RG (1 *** 2 +++ 1 *** 3)).
Proof.
    unfold sameDistance.
    apply bothOneStep.
    apply bothInStart.
    - simpl. unfold RG_reachableInOneStep. exists 1, tt. firstorder.
    - simpl. unfold RG_reachableInOneStep. exists 1, tt. firstorder.
Qed.


(* Returns true, if the distance from a1 to start is one plus the distance from a2 to start *)
Definition distanceSecondOneLower {A B : Type} (start : Ensemble A) (a1 a2 : A) (rg : RG A B) : Prop :=
    sameDistance_rec rg (fun x => RG_reachableInOneStep start x rg) a1 start a2.

    
Lemma distanceSecondOneLower_test1 : distanceSecondOneLower (fun x => x = 1) 4 2 (AG_to_RG (1 *** 2 +++ 1 *** 3 +++ 3 *** 4)).
Proof.
    unfold distanceSecondOneLower.
    apply bothOneStep.
    apply bothInStart.
    - simpl. unfold RG_reachableInOneStep. exists 3, tt. firstorder. exists 1, tt. firstorder.
    - simpl. unfold RG_reachableInOneStep. exists 1, tt. firstorder.
Qed.





Inductive revBFS_Order {B : Type} (start : NatSet.t) (rg : RG nat B) : list nat -> Prop :=
    | revBFS_Order_start (l : list nat) : Permutation (NatSet.elements start) l -> revBFS_Order start rg l

    | revBFS_Order_same (noww next : nat) (l : list nat) :
        sameDistance (fun x => NatSet.In x start) noww next rg -> revBFS_Order start rg (next :: l) -> revBFS_Order start rg (noww :: next :: l)   

    | revBFS_Order_next (noww next : nat) (l : list nat) :
        distanceSecondOneLower  (fun x => NatSet.In x start) noww next rg 
        -> revBFS_Order start rg (next :: l) -> revBFS_Order start rg (noww :: next :: l).

Definition BFS_Order {B : Type} (startL result : list nat) (rg : RG nat B) :=
    revBFS_Order (NatSet_fromList startL) rg (rev result).


(* Actual specification about the order of nodes from BFS *)
Theorem AG_BFS_order : forall (nodes : list nat) (ag : AG nat),
    BFS_Order nodes (AG_BFS nodes ag) (AG_to_RG ag).
Proof.
    intros.
Admitted.


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

