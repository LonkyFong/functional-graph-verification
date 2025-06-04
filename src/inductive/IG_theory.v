Require Import Coq.micromega.Lia.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

Require Import Coq.Arith.Arith.

Require Import List.
Import ListNotations.

Require Import GraphVerification.src.util.util.
Require Import GraphVerification.src.util.NatSet.
Require Import GraphVerification.src.util.NatMap.

Require Import GraphVerification.src.RG.
Require Import GraphVerification.src.RG_theory.

Require Import GraphVerification.src.inductive.IG.




(* Stating and proving Lemmas and Theorems (an an equational manner) about IG functions that do not use well_founded induction.
For those, go to inductive_graph_measured_algorithms_theory
 *)

 
Definition _key_In_IG {A B : Type} (node : Node) (ig : IG A B) : Prop := 
    (exists other, In (node, other) (IG_labNodes ig)).


(* Start with the most basic properties about IG_empty *)
Theorem IG_empty_isEmpty : forall (A B : Type),
    IG_isEmpty (@IG_empty A B) = true.
Proof.
    compute. reflexivity.
Qed.

Theorem IG_labNodes_empty_nil : forall (A B : Type),
    IG_labNodes (@IG_empty A B) = [].
Proof.
    compute. reflexivity.
Qed.




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






(* Here start "meaningful statements" *)

(* Section on statements about _updateEntry and _updAdj *)

(* Two general Lemmas about _updateEntry and _updAdj using any function f *)
Lemma _updateEntry_does_not_change_key_set : forall (A B : Type) (node : Node) (f : Context' A B -> Context' A B) (ig : IG A B) (x : Node),
    _key_In_IG x (_updateEntry node f ig) <-> _key_In_IG x ig. 
Proof.
    intros. unfold _updateEntry.
    destruct (NatMap.find node ig) eqn:isIn.
    - destruct_context' c. destruct_contextt' (f (froms', label', tos')). apply MFacts.find_mapsto_iff in isIn.
        firstorder.
        + apply _In_labNodes_is_some_MapsTo in H. simpl in *. destruct_eMapsTo H.
            apply MFacts.add_mapsto_iff in H. firstorder.
            -- subst. exists label'. apply _In_labNodes_is_some_MapsTo. firstorder.
            -- exists x0. apply _In_labNodes_is_some_MapsTo. firstorder.
        + bdestruct (node =? x).
            -- subst. exists labell'. apply _In_labNodes_is_some_MapsTo. exists fromss', toss'.
                apply MFacts.add_mapsto_iff. firstorder.
            -- apply _In_labNodes_is_some_MapsTo in H.
                exists x0. apply _In_labNodes_is_some_MapsTo.
                destruct_eMapsTo H. exists efroms, etos.
                apply MFacts.add_mapsto_iff.
                firstorder.

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
which all don't actually change the label. When used with _updateEntry and _updAdj *)
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


(* Unproved Lemmas, to convert IG_labNodes to IG_match *)
Lemma IG_match_is_In_IG_labNodes : forall (A B : Type) (x : LNode A) (ig : IG A B),
    In x (IG_labNodes ig)
        <-> let '(query, label) := x in
        (exists froms tos hit i, IG_match query ig = (Some (froms, hit, label, tos), i)).
Proof.
Admitted.


Lemma IG_match_hit_is_key : forall (A B : Type) (query : Node) (ig : IG A B), 
    _key_In_IG query ig <-> exists c i, IG_match query ig = (Some c, i).  
Proof.
Admitted.



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





Theorem IG_match_empty_is_nothing : forall (A B : Type) (node : Node),
    IG_match node (@IG_empty A B) = (None, IG_empty).   
Proof.
    intros. compute. reflexivity.
Qed.



Lemma IG_match_returns_valid_neighbours : forall (A B : Type) (query : Node) (ig i : IG A B) (c : Context A B) (n : Node),
    let '(froms, hit, label, tos) := c in
    IG_match query ig = (Some (froms, hit, label, tos), i)
        -> (In n (map snd froms) \/ In n (map snd tos))
        -> _key_In_IG n  i.  
Proof.
Admitted.



