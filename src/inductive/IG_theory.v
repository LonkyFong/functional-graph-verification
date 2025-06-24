Require Import Lia.

Require Import Arith.

Require Import List.
Import ListNotations.

Require Import GraphVerification.src.util.util.
Require Import GraphVerification.src.util.NatSet.
Require Import GraphVerification.src.util.NatMap.

Require Import GraphVerification.src.relational.RG.
Require Import GraphVerification.src.relational.RG_theory.

Require Import GraphVerification.src.inductive.IG.


(** Stating and proving basic Lemmas and Theorems (an an equational manner) about IG functions that do not use well_founded induction.
    Start with very useful "_In_labNodes_is_some_MapsTo" and then moves on to showing how "match" and "and" work on nodes.
    Then some statements about IG_isEmpty and when IG_labNodes is empty.
    For theorems on functions using well_founded induction, go to "inductive_graph_measured_operations_theory" *)



(* Block to derive useful conversion theorem "In_labNodes_is_InMap" *)

(* Helper lemma for converting an In (of a map) to an InA, which will eventually be turned to a NatMap.In (which has useful lemmas)  *)
Lemma _In_map_some_InA : forall (A B: Type) (x : LNode A) (l : list (Node * (Context' A B))),
    In x (map (fun '(v, (_, l, _)) => (v, l)) l)
        <-> exists (froms tos : Adj B), InA (fun (e1 e2 : (Node * (Context' A B))) => NatMap.eq_key_elt e1 e2) (fst x, (froms, snd x, tos)) l.  
Proof.
    intros. induction l; simpl.
    - firstorder. inversion H.
    - destruct x as [xn xc]. destruct a as [n c']. destruct_context' c'.
        rewrite IHl. clear IHl. simpl.
        firstorder.
        + inversion H. subst. exists froms', tos'. apply InA_cons. firstorder.
        + exists x, x0. apply InA_cons. firstorder.
        + apply InA_cons in H. firstorder. left. simpl in *. inversion H0. subst. reflexivity.
Qed.
        

(* This is the most useful one for proving other statements.
    Use it to convert from "use friendly" In- statements to "provable" NatMap.In- statements  *)
Lemma _In_labNodes_is_some_MapsTo : forall (A B : Type) (x : LNode A) (ig : IG A B),
    In x (IG_labNodes ig) <-> exists froms tos, NatMap.MapsTo (fst x) (froms, snd x, tos) ig.     
Proof.
    intros. unfold IG_labNodes.
    rewrite _In_map_some_InA.
    firstorder.
    - apply MFacts.elements_mapsto_iff in H. firstorder.
    - apply MFacts.elements_mapsto_iff in H. firstorder.
Qed.

(* Useful for destructing arising existential statements *)
Ltac destruct_eMapsTo H := destruct H as [efroms [etos H]].

(* This is a nice way to write statements about the existence of a node in an IG *)
Definition _key_In_IG {A B : Type} (node : Node) (ig : IG A B) : Prop := 
    (exists other, In (node, other) (IG_labNodes ig)).

(* The above is defined using "user-level" operations. For provability, it is nice to convert to NatMap.mem *)
Lemma _key_In_IG_mem_iff : forall (A B : Type) (node : Node) (ig : IG A B),
    _key_In_IG node ig <-> NatMap.mem node ig = true.
Proof.
    intros.
    unfold _key_In_IG.
    setoid_rewrite _In_labNodes_is_some_MapsTo.
    pose proof NatMap_In_exists_MapsTo_iff.
    rewrite <- MProps.F.mem_in_iff.
    rewrite NatMap_In_exists_MapsTo_iff.
    firstorder. destruct_context' x. firstorder.
Qed.



(* Here start "meaningful statements" *)

(* Section on statements about _updateEntry and _updAdj *)

(* Two general Lemmas about _updateEntry and _updAdj using any function f.
    They don't change the key set of the IG *)
Lemma _updateEntry_does_not_change_key_set : forall (A B : Type) (node : Node) (f : Context' A B -> Context' A B) (ig : IG A B) (x : Node),
    _key_In_IG x (_updateEntry node f ig) <-> _key_In_IG x ig. 
Proof.
    intros. rewrite !_key_In_IG_mem_iff. unfold _updateEntry.
    destruct (NatMap.find node ig) eqn:isIn.
    - assert (NatMap.In node ig). {
        apply <- MFacts.in_find_iff.
        rewrite isIn. unfold not. intros. inversion H.
    } rewrite <- !MFacts.mem_in_iff. rewrite MFacts.add_in_iff. bdestruct (node =? x).
        + subst. firstorder.
        + firstorder.
    - reflexivity.
Qed.



Lemma _updAdj_does_not_change_key_set : forall (A B : Type) (adj : Adj B) (f : B -> Context' A B -> Context' A B) (ig : IG A B) (x : Node), 
    _key_In_IG x (_updAdj adj f ig) <-> _key_In_IG x ig. 
Proof.
    intros. unfold _updAdj.
    induction adj; simpl.
    - reflexivity.
    - destruct a. rewrite _updateEntry_does_not_change_key_set. rewrite <- IHadj. reflexivity.
Qed.




(* Generalization of properties of _addSucc, _addPred, _clearSucc and _clearPred
    which all don't actually change the label as well. When used with _updateEntry and _updAdj *)
Lemma _updateEntry_sameLabel_f_does_not_change_IG_labNodes : forall (A B : Type) (node : Node) (f : Context' A B -> Context' A B) (ig : IG A B) (x : LNode A),
    (forall (c : Context' A B),
        let '(_, label, _) := c in
        let '(_, label', _) := (f c) in
        label = label')
        -> In x (IG_labNodes (_updateEntry node f ig)) <-> In x (IG_labNodes ig).    
Proof.
    intros. unfold _updateEntry.
    destruct (NatMap.find node ig) eqn:isIn.
    - specialize (H c). destruct_context' c. destruct_contextt' (f (froms', label', tos')).
        destruct x as [xn xl].
        apply MFacts.find_mapsto_iff in isIn.
        rewrite !_In_labNodes_is_some_MapsTo. simpl in *. firstorder.
        + apply MFacts.add_mapsto_iff in H0. firstorder. simpl in *. inversion H1. subst. firstorder.
        + bdestruct (xn =? node).
            -- subst. exists fromss', toss'. apply MFacts.add_mapsto_iff. left.
                pose proof (NatMap_MapsTo_same_key_same_value _ _ _ _ isIn H0). inversion H. firstorder.
            -- exists x, x0. apply MFacts.add_mapsto_iff. right. firstorder.
    - reflexivity.
Qed.


Lemma _updAdj_sameLabel_f_does_not_change_IG_labNodes : forall (A B : Type) (f : B -> Context' A B -> Context' A B) (adj : Adj B) (ig : IG A B) (x : LNode A), 
    (forall (b : B) (c : Context' A B),
        let '(_, label, _) := c in
        let '(_, label', _) := (f b c) in
        label = label')    
    -> In x (IG_labNodes (_updAdj adj f ig)) <-> In x (IG_labNodes ig).
Proof.
    intros. unfold _updAdj.
    induction adj; simpl.
    - reflexivity.
    - destruct a. rewrite _updateEntry_sameLabel_f_does_not_change_IG_labNodes.
        + assumption.
        + intros. apply H.
Qed.




(* Now apply the general proof to instances _addSucc, _addPred, _clearSucc and _clearPred *)
Ltac _updateEntry_instance_prover c := intros; apply _updateEntry_sameLabel_f_does_not_change_IG_labNodes; intros; destruct_context' c; firstorder.
Ltac _updAdj_instance_prover c := intros; apply _updAdj_sameLabel_f_does_not_change_IG_labNodes; intros; destruct_context' c; firstorder.


(* _addSucc *)
Lemma _updateEntry_addSucc_does_not_change_IG_labNodes : forall (A B : Type) (node whose : Node) (l : B) (ig : IG A B) (x : LNode A),
    In x (IG_labNodes (_updateEntry node (_addSucc whose l) ig)) <-> In x (IG_labNodes ig).    
Proof.
    _updateEntry_instance_prover c.
Qed.

Lemma _updAdj_addSucc_does_not_change_IG_labNodes : forall (A B : Type) (node : Node) (adj : Adj B) (ig : IG A B) (x : LNode A), 
    In x (IG_labNodes (_updAdj adj (_addSucc node) ig)) <-> In x (IG_labNodes ig).
Proof.
    _updAdj_instance_prover c.
Qed.


(* _addPred *)
Lemma _updateEntry_addPred_does_not_change_IG_labNodes : forall (A B : Type) (node whose : Node) (l : B) (ig : IG A B) (x : LNode A),
    In x (IG_labNodes (_updateEntry node (_addPred whose l) ig)) <-> In x (IG_labNodes ig).    
Proof.
    _updateEntry_instance_prover c.

Qed.

Lemma _updAdj_addPred_does_not_change_IG_labNodes : forall (A B : Type) (node : Node) (adj : Adj B) (ig : IG A B) (x : LNode A), 
    In x (IG_labNodes (_updAdj adj (_addPred node) ig)) <-> In x (IG_labNodes ig).
Proof.
    _updAdj_instance_prover c.
Qed.


(* _clearSucc *)
Lemma _updateEntry_clearSucc_does_not_change_IG_labNodes : forall (A B : Type) (node whose : Node) (ig : IG A B) (x : LNode A),
    In x (IG_labNodes (_updateEntry node (_clearSucc whose) ig)) <-> In x (IG_labNodes ig).   
Proof.
    _updateEntry_instance_prover c.
Qed.

Lemma _updAdj_clearSucc_does_not_change_IG_labNodes : forall (A B : Type) (node : Node) (adj : Adj B)  (ig : IG A B) (x : LNode A),  
    In x (IG_labNodes
        (_updAdj adj (fun _ y => _clearSucc node y)
    ig)) <-> In x (IG_labNodes ig).
Proof.
    _updAdj_instance_prover c.
Qed.


(* _clearPred *)
Lemma _updateEntry_clearPred_does_not_change_IG_labNodes : forall (A B : Type) (node whose : Node) (ig : IG A B) (x : LNode A),
    In x (IG_labNodes (_updateEntry node (_clearPred whose) ig)) <-> In x (IG_labNodes ig).     
Proof.
    _updateEntry_instance_prover c.
Qed.

Lemma _updAdj_clearPred_does_not_change_IG_labNodes : forall (A B : Type) (node : Node) (adj : Adj B)  (ig : IG A B) (x : LNode A), 
    In x (IG_labNodes
        (_updAdj adj (fun _ y => _clearPred node y)
    ig)) <-> In x (IG_labNodes ig).
Proof.
    _updAdj_instance_prover c.
Qed.




(* Some theorems about IG_match *)

Lemma IG_match_removes_node : forall (A B : Type) (query : Node) (mContext : MContext A B) (ig i : IG A B),
    IG_match query ig = (mContext, i)
        -> not (_key_In_IG query i). 
Proof.
    intros. unfold not. intros. destruct H0.
    unfold IG_match in H. destruct (NatMap.find query ig) eqn:HH.
    - unfold _cleanSplit in H. destruct_context' c. inversion H. clear H H2. rewrite <- H3 in H0. clear H3.
        apply _updAdj_clearPred_does_not_change_IG_labNodes in H0.
        apply _updAdj_clearSucc_does_not_change_IG_labNodes in H0.

        apply _In_labNodes_is_some_MapsTo in H0. destruct_eMapsTo H0. simpl in H0.
        apply MFacts.remove_mapsto_iff in H0. firstorder.
        
    
    - inversion H. subst. apply MFacts.not_find_in_iff in HH. apply _In_labNodes_is_some_MapsTo in H0.
        firstorder.
Qed.


Lemma IG_match_exactly_removes_node : forall (A B : Type) (query : Node) (c : Context A B) (ig i : IG A B) (x : LNode A),
    IG_match query ig = (Some c, i)
        -> In x (IG_labNodes ig)
                <-> let '(_, hit, label, _) := c in (x = (hit, label) /\ ~_key_In_IG (fst x) i) \/ In x (IG_labNodes i).
Proof.
    intros. simpl.
    unfold IG_match in H. destruct (NatMap.find query ig) eqn:found.
    -  apply MFacts.find_mapsto_iff in found.
        unfold _cleanSplit in H. destruct_context c. destruct_context' c0. destruct x as [xn xl]. inversion H. subst. clear H.

        unfold _key_In_IG in *.
        (* This used to be much more spread out, until it got compacted *)
        setoid_rewrite _updAdj_clearPred_does_not_change_IG_labNodes.
        setoid_rewrite _updAdj_clearSucc_does_not_change_IG_labNodes.
        setoid_rewrite _In_labNodes_is_some_MapsTo.
        setoid_rewrite MFacts.remove_mapsto_iff.
        split; intros.
        + bdestruct (node =? xn).
            -- subst. left. split.
                ++ f_equal. simpl in H. destruct_eMapsTo H.
                    pose proof (NatMap_MapsTo_same_key_same_value _ _ _ _ found H).
                    inversion H0. reflexivity.

                ++ simpl. firstorder.
            -- simpl. firstorder.
        + destruct H.
            -- exists froms', tos.
                destruct H. inversion H. subst. assumption.
            -- firstorder.    
    - inversion H.
Qed.



Lemma IG_match_empty_is_nothing : forall (A B : Type) (node : Node),
    IG_match node (@IG_empty A B) = (None, IG_empty).   
Proof.
    intros. compute. reflexivity.
Qed.

Lemma IG_matchAny_None_is_empty : forall (A B : Type) (ig i : IG A B),
    IG_matchAny ig = (None, i) -> IG_isEmpty ig = true.
Proof.
    intros.
    unfold IG_matchAny in H.
    unfold IG_isEmpty.
    destruct (IG_labNodes ig) eqn:labNodes.
    - apply map_eq_nil in labNodes.
        apply MProps.elements_Empty in labNodes.
        apply MFacts.is_empty_iff in labNodes.
        assumption.
    - unfold IG_match in H. destruct l. simpl in *. destruct (NatMap.find n ig) eqn:found.
        + destruct (_cleanSplit n c (NatMap.remove n ig)). inversion H.
        + unfold IG_labNodes in labNodes.
            assert (exists e, InA (@NatMap.eq_key_elt _) (n, e) (NatMap.elements ig)). {
                pose proof (in_eq (n, a) l0). setoid_rewrite  <- labNodes in H0. clear labNodes found.
                apply _In_map_some_InA in H0. firstorder.
            }
            apply MFacts.elements_in_iff in H0. clear labNodes.
            apply MFacts.not_find_in_iff in found.
            firstorder.
Qed.



Lemma IG_and_adds_node : forall (A B : Type) (c : Context A B) (ig : IG A B) (x : LNode A),
    In x (IG_labNodes (c &I ig))
        <-> let '(_, node, label, _) := c in (x = (node, label) /\ ~_key_In_IG (fst x) ig) \/ In x (IG_labNodes ig).
Proof.
    intros. destruct_context c. unfold _key_In_IG.
    unfold IG_and.
    destruct (NatMap.mem node ig) eqn:cond.
    - split; intros.
        + firstorder.
        + destruct H.
            -- destruct H. unfold not in H0. exfalso. apply H0. clear H0. destruct x as [xn xl]. inversion H. subst.
                apply MFacts.mem_in_iff in cond.
                apply -> NatMap_In_exists_MapsTo_iff in cond. destruct cond. destruct_context' x.
                exists label'.
                apply _In_labNodes_is_some_MapsTo. simpl. firstorder.
            -- assumption.
    - rewrite _updAdj_addSucc_does_not_change_IG_labNodes.
        rewrite _updAdj_addPred_does_not_change_IG_labNodes.
        rewrite _In_labNodes_is_some_MapsTo. destruct x as [xn xl]. 
        simpl.

        setoid_rewrite MFacts.add_mapsto_iff.
        rewrite _In_labNodes_is_some_MapsTo.
        apply MFacts.not_mem_in_iff in cond.
        simpl.
        firstorder. 
        + inversion H1. subst. left. firstorder. unfold not. 
            setoid_rewrite _In_labNodes_is_some_MapsTo. firstorder.
        + inversion H0. subst. exists froms, tos. firstorder.
        + bdestruct (node =? xn).
            -- subst. firstorder.
            -- firstorder.
Qed.


Lemma IG_and_adds_key : forall (A B : Type) (c : Context A B) (ig : IG A B) (n : Node),
    let '(from, node, label, tos) := c in
    _key_In_IG n (c &I ig) <-> n = node \/ _key_In_IG n ig.
Proof.
    intros. destruct_context c. unfold _key_In_IG. setoid_rewrite IG_and_adds_node.
    destruct (NatMap.mem n ig) eqn:cond.
    - rewrite <- _key_In_IG_mem_iff in cond. unfold _key_In_IG in cond. firstorder.
    - assert (~ (NatMap.mem n ig = true)). {
            rewrite cond. firstorder.
        }
        clear cond. rewrite <- _key_In_IG_mem_iff in H.
        unfold _key_In_IG in H. firstorder.
        + inversion H0. subst. auto.
        + exists label. subst. firstorder.
Qed.



(* Some Theorems about IG_isEmpty and in which cases IG_labNodes is empty: *)


(* But first one helper lemma for showing that some and is not empty for various checks *)
Lemma _exists_x_in_and : forall (A B : Type) (c : Context A B) (ig : IG A B),
    exists x, In x (IG_labNodes (c &I ig)).
Proof.
    intros.
    setoid_rewrite IG_and_adds_node.
    destruct_context c.
    destruct (NatMap.mem node ig) eqn:cond.
    - rewrite <- _key_In_IG_mem_iff in cond.
        firstorder.
    - assert (not (NatMap.mem node ig = true)). { 
            unfold not. intros. rewrite H in cond. inversion cond.
        } clear cond. rewrite <- _key_In_IG_mem_iff in H.
        exists (node, label).
        firstorder.
Qed.



Theorem IG_empty_isEmpty : forall (A B : Type),
    IG_isEmpty (@IG_empty A B) = true.
Proof.
    compute. reflexivity.
Qed.


Theorem IG_and_not_isEmpty : forall (A B : Type) (c : Context A B) (ig : IG A B),
    IG_isEmpty (c &I ig) = false.
Proof.
    intros. unfold IG_isEmpty. 
    apply NatMap_not_Empty_is_empty_false. unfold not. intros.
    apply MProps.elements_Empty in H.
    assert (forall x, ~In x (IG_labNodes (c &I ig))). {
        intros. unfold not. intros.
        assert (IG_labNodes (c &I ig) = []). {
            clear H0.
            unfold IG_labNodes. rewrite H.
            reflexivity.
        }
        rewrite H1 in H0.
        apply in_nil in H0.
        inversion H0.
    }
    clear H.
    pose proof (_exists_x_in_and _ _ c ig).
    destruct H.
    firstorder.
Qed.



Theorem IG_labNodes_empty_nil : forall (A B : Type),
    IG_labNodes (@IG_empty A B) = [].  
Proof.
    compute. reflexivity.
Qed.

Theorem IG_labNodes_and_not_nil : forall (A B : Type) (c : Context A B) (ig : IG A B),
    IG_labNodes (c &I ig) <> [].
Proof.
    intros. unfold not. intros.
    assert (forall x, ~In x (IG_labNodes (c &I ig))). {
        rewrite H. apply in_nil.
    }
    clear H.
    pose proof (_exists_x_in_and _ _ c ig).
    destruct H.
    firstorder.
Qed.

