Require Import Lia.

Require Import Arith.

Require Import List.
Import ListNotations.

Require Import GraphVerification.src.util.util.
Require Import GraphVerification.src.util.NatMap.

Require Import GraphVerification.src.RG.
Require Import GraphVerification.src.RG_theory.

Require Import GraphVerification.src.inductive.IG.
Require Import GraphVerification.src.inductive.IG_wf.
Require Import GraphVerification.src.inductive.IG_theory.

(* Stating and proving Lemmas and Theorems about IG_mkGraph and helper functions *)


(* Here, one may consider using IG_match as a probing tool instead of IG_labNodes *)
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


Lemma _insNode_any_ins_node : forall (A B : Type) (node : LNode A) (ig : IG A B) (x : LNode A),
    In x (IG_labNodes (_insNode node ig)) <-> (x = node /\ ~_key_In_IG (fst x) ig ) \/ In x (IG_labNodes ig).
Proof.
    intros.
    unfold _insNode.
    destruct node. intros.
    pose proof (IG_and_adds_node _ B (nil, n, a, nil)).
    apply H.
Qed.



(* Two helpers for "_insNodes_any_ins_all_nodes" *)
Lemma _MapsTo_same_on_different_insNodes : forall (A B : Type) (n : Node) (a : A) (nodes : list (LNode A)) (ig : IG A B),
    ~ InA (fun x y : Node * A => fst x = fst y) (n, a) nodes
        -> forall c, NatMap.MapsTo n c (_insNodes nodes ig) <-> NatMap.MapsTo n c ig.  
Proof.
    intros. induction nodes; simpl.
    - reflexivity.
    - destruct a0. assert (~ InA (fun x y => fst x = fst y) (n, a) nodes). {
            firstorder.
        } specialize (IHnodes H0).
        assert (n0 <> n). {
            firstorder.
        }
        unfold _insNode. unfold IG_and.
        destruct (NatMap.mem n0 (_insNodes nodes ig)) eqn:split.
        + apply IHnodes.
        + simpl. rewrite MFacts.add_mapsto_iff. firstorder.
Qed.



Lemma _key_In_IG_same_on_different_insNodes : forall (A B : Type) (n : Node) (a : A) (nodes : list (LNode A)) (ig : IG A B),
    ~ InA (fun x y : Node * A => fst x = fst y) (n, a) nodes
        -> ~_key_In_IG n (_insNodes nodes ig) <-> ~_key_In_IG n ig.
Proof.
    intros.
    unfold _key_In_IG.
    setoid_rewrite _In_labNodes_is_some_MapsTo.
    simpl.
    unfold not.
    split; intros; apply H0; destruct H1; destruct_eMapsTo H1;
    exists x, efroms, etos; eapply _MapsTo_same_on_different_insNodes in H; apply H; apply H1.
Qed.




Lemma _insNodes_any_ins_all_nodes : forall (A B : Type) (nodes : list (LNode A)) (ig : IG A B) (x : LNode A),
    NoDupA (fun x y => fst x = fst y) nodes
        -> In x (IG_labNodes (_insNodes nodes ig)) <-> (In x nodes /\ ~_key_In_IG (fst x) ig) \/ In x (IG_labNodes ig).
Proof.
    intros. induction nodes; simpl.
    - firstorder.
    - inversion H. subst. specialize (IHnodes H3). clear H. destruct a as [an al].
        rewrite _insNode_any_ins_node. rewrite IHnodes. clear IHnodes. split; intros.
        (* This could probably be compacted, but the performance of firstorder is not good enough in this case *)
        + destruct H.
            -- destruct H. left.  destruct x as [xn xl]. inversion H. subst.
                split.
                ++ firstorder.
                ++ eapply _key_In_IG_same_on_different_insNodes in H2.
                    apply H2.
                    apply H0. 
                
            -- firstorder.
        + destruct H.
            -- destruct H. destruct H.
                ++ left. destruct x. inversion H. subst. split.
                    --- reflexivity.
                    --- eapply _key_In_IG_same_on_different_insNodes in H2.
                        apply H2.
                        apply H0.
                ++ firstorder.
            -- firstorder.
Qed.




Lemma _insEdge_does_not_add_node : forall (A B : Type) (edge : LEdge B) (ig : IG A B) (x : LNode A),
    In x (IG_labNodes (_insEdge edge ig)) <-> In x (IG_labNodes ig).
Proof.
    intros. unfold _insEdge. destruct_edge edge.
    
    destruct (IG_match from ig) eqn:mat.
    destruct m.
    - destruct_context c. rewrite IG_and_adds_node.
        destruct (NatMap.mem from i) eqn:mem.
        + exfalso. apply IG_match_removes_node in mat. apply mat. clear mat.
            unfold _key_In_IG.
            apply  MFacts.mem_in_iff in mem.
            apply -> NatMap_In_exists_MapsTo_iff in mem.
            destruct mem. destruct_context' x0.
            setoid_rewrite _In_labNodes_is_some_MapsTo.
            firstorder.
        + apply IG_match_returns_node in mat as mat'. subst.
            apply (IG_match_exactly_removes_node _ _ _ _ _ _  x) in mat. rewrite mat. reflexivity.
    - reflexivity.
Qed.


Lemma _insEdges_does_not_add_nodes : forall (A B : Type) (edges : list (LEdge B)) (ig : IG A B) (x : LNode A), 
    In x (IG_labNodes (_insEdges edges ig)) <-> In x (IG_labNodes ig).
Proof.
    intros. simpl. induction edges; simpl.
    - reflexivity.
    - rewrite _insEdge_does_not_add_node. rewrite IHedges. reflexivity.
Qed. 

Lemma _insEdge_on_empty_is_empty : forall (A B : Type) (edge : LEdge B),
    _insEdge edge (@IG_empty A B) = IG_empty. 
Proof.
    intros. destruct_edge edge. compute. reflexivity.
Qed.


Lemma _insEdges_on_empty_is_empty : forall (A B : Type) (edges : list (LEdge B)),
    _insEdges edges (@IG_empty A B) = IG_empty.
Proof.
    intros. induction edges; simpl.
    - reflexivity.
    - rewrite IHedges. rewrite _insEdge_on_empty_is_empty. reflexivity.
Qed.


(* Quite interesting, compound statement about IG_mkGraph *)
Theorem IG_mkGraph_any_ins_all_nodes : forall (A B : Type) (nodes : list (LNode A)) (edges : list (LEdge B)) (x : LNode A),
    NoDupA (fun x y => fst x = fst y) nodes
        -> In x (IG_labNodes (IG_mkGraph nodes edges)) <-> In x nodes.
Proof.
    intros. unfold IG_mkGraph. rewrite _insEdges_does_not_add_nodes. rewrite _insNodes_any_ins_all_nodes.
    - firstorder.
    - assumption.
Qed.



Theorem IG_non_empty_isEmpty_false : forall (A B : Type) (nodes : list (LNode A)) (edges : list (LEdge B)),
    NoDupA (fun x y => fst x = fst y) nodes
        -> length nodes <> 0 <-> IG_isEmpty (IG_mkGraph nodes edges) = false.
Proof.
    intros. unfold IG_isEmpty. rewrite <- _not_NatMap_Empty_is_empty_false. unfold not. unfold IG_mkGraph.
    destruct nodes; simpl.
    - rewrite _insEdges_on_empty_is_empty.
        rewrite MProps.elements_Empty. firstorder.

    - split; intros.
        + apply MProps.elements_Empty in H1.
            
            apply (IG_mkGraph_any_ins_all_nodes _ B _ edges l) in H.
            pose proof in_eq.
            apply H in H2. clear H.

            rewrite _In_labNodes_is_some_MapsTo in H2.
            destruct_eMapsTo H2.
            
            apply -> MFacts.elements_mapsto_iff in H2.

            unfold IG_mkGraph in H2.
            assert (NatMap.elements (elt:=Adj B * A * Adj B) (_insEdges edges (_insNodes (l :: nodes) IG_empty)) = []). {
                assumption.
            }
            rewrite  H in H2. inversion H2.
        + congruence.
Qed.
