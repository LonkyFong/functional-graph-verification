Require Import Coq.micromega.Lia.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

Require Import Coq.Arith.Arith.

Require Import List.
Require Import Coq.Structures.OrdersTac.
Require Import Bool.
Import ListNotations.

Require Import FSets.
Require Import FMaps.
Require Import OrderedTypeEx.
Require Import Setoid Morphisms.

Require Import GraphVerification.src.util.NatSet.

Require Import GraphVerification.src.inductive.IG.
Require Import GraphVerification.src.inductive.IG_wf.
Require Import GraphVerification.src.inductive.IG_theory.

Require Import GraphVerification.src.RG.
Require Import GraphVerification.src.RG_theory.

Require Import GraphVerification.src.util.NatMap.
Require Import GraphVerification.src.util.util.

(* Stating and proving Lemmas and Theorems about IG_mkGraph and helper functions *)



(* Here, one may consider using IG_match as a probing tool instead of IG_labNodes *)
Lemma IG_and_adds_node : forall (A B : Type) (c : Context A B) (ig : IG A B) (x : LNode A),
    In x (IG_labNodes (IG_and c ig))
        <-> let '(_, node, label, _) := c in (x = (node, label) /\ ~_key_In_IG (fst x) ig) \/ In x (IG_labNodes ig).
Proof.
    intros.
    destruct_context c.

    unfold _key_In_IG.
    unfold IG_and.
    destruct (NatMap.mem node ig) eqn:cond.
    - split; intros.
        + firstorder.
        + destruct H.
            -- destruct H. unfold not in H0. exfalso. apply H0. destruct x as [xn xl]. inversion H. subst.
                apply MFacts.mem_in_iff in cond.
                apply -> NatMap_In_exists_MapsTo_iff in cond. destruct cond. destruct_context' x.
                exists label'.
                apply _In_labNodes_is_some_MapsTo. firstorder.
            -- assumption.
    - rewrite _updAdj_addSucc_does_not_change_IG_labNodes.
        rewrite _updAdj_addPred_does_not_change_IG_labNodes.
        rewrite _In_labNodes_is_some_MapsTo. destruct x as [xn xl]. 
        simpl.

        (* This allows for rewriting within an exists *)
        setoid_rewrite MFacts.add_mapsto_iff.
        rewrite _In_labNodes_is_some_MapsTo.
        apply MFacts.not_mem_in_iff in cond.
        simpl.
        firstorder. 
        + inversion H1. subst. left. split.
            -- reflexivity.

            -- unfold not. intros. destruct H0.
                apply _In_labNodes_is_some_MapsTo in H0.
                firstorder.
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




Lemma _MapsTo_same_on_different_insNodes : forall (A B : Type) (n : Node) (a : A) (nodes : list (LNode A)) (ig : IG A B),
    ~ InA (fun x y : NatSet.Node * A => fst x = fst y) (n, a) nodes
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
    ~ InA (fun x y : NatSet.Node * A => fst x = fst y) (n, a) nodes ->
    ~_key_In_IG n (_insNodes nodes ig) <-> ~_key_In_IG n ig.
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
        +
        (* apply (_mem_different_insNodes A B _ _ _ ig) in H2. *)
            destruct H.
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
  intros. unfold _insEdge. destruct edge as [[from to] label].
  destruct (IG_match from ig) eqn:HH.
  destruct m as [[[[froms n] l] tos] | ].
  - rewrite IG_and_adds_node. destruct (NatMap.mem from i) eqn:HHH.
    + exfalso. apply IG_match_returns_node in HH as HHHH. subst.
      apply  MFacts.mem_in_iff in HHH.
      
      assert (exists c, NatMap.MapsTo n c i). {
        firstorder.
      }
      destruct H as [[[fromss node] toss] H].

      assert (In (n, node) (IG_labNodes i)). {
        apply _In_labNodes_is_some_MapsTo. firstorder.
      }

      eapply IG_match_removes_node in HH.
      unfold not in HH. apply HH. exists node. apply H0.


    + simpl. apply IG_match_returns_node in HH as HHHH. subst.
        apply (IG_match_exactly_removes_node _ _ _ _ _ _  x) in HH. rewrite HH. simpl. reflexivity.
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
    _insEdge edge (@IG_empty A B)= IG_empty. 
(* This proof is very similar to "insEdge_does_not_add_node", but using it here it is more complicated than just doing it again  *)
Proof.
    intros. compute. destruct edge as [[_ _] _]. reflexivity.
Qed.


Lemma _insEdges_on_empty_is_empty : forall (A B : Type) (edges : list (LEdge B)),
    _insEdges edges (@IG_empty A B) = IG_empty.
(* This proof is very similar to "insEdges_does_not_add_nodes", but using it here it is more complicated than just doing it again  *)
Proof.
    intros. induction edges; simpl.
    - reflexivity.
    - rewrite IHedges. rewrite _insEdge_on_empty_is_empty. reflexivity.
Qed.

Lemma _filter_identity : forall (A B: Type) (l : list (A * B)),
    filter (fun '(_, _) => true) l = l.
Proof.
    intros. rewrite forallb_filter_id.
        + reflexivity.
        + induction l.
        -- simpl. reflexivity.
        -- simpl. rewrite IHl.
            ++ destruct a. simpl. reflexivity.
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

Lemma _not_NatMap_Empty_is_empty_false : forall (A : Type) (m : NatMap.t A),
    not (NatMap.Empty m) <-> NatMap.is_empty m = false.
Proof.
    intros. unfold not. rewrite MFacts.is_empty_iff. destruct (NatMap.is_empty (elt:=A) m) eqn:cond.
    - firstorder. congruence.
    - firstorder. congruence.
Qed.


Theorem  IG_non_empty_isEmpty_false : forall (A B : Type) (nodes : list (LNode A)) (edges : list (LEdge B)),
    NoDupA (fun x y => fst x = fst y) nodes ->
    length nodes <> 0 <-> IG_isEmpty (IG_mkGraph nodes edges) = false.
Proof.
    intros. unfold IG_isEmpty. rewrite <- _not_NatMap_Empty_is_empty_false. unfold not.
    destruct nodes; simpl; unfold IG_mkGraph.
    - simpl. rewrite _insEdges_on_empty_is_empty.
        rewrite MProps.elements_Empty. compute. firstorder.

    - simpl. split; intros.
        + apply MProps.elements_Empty in H1.
        assert (HH : not (exists (froms tos : Adj B), InA (fun (e1 e2 : (Node * (Context' A B))) => NatMap.eq_key_elt e1 e2) (fst l, (froms, snd l, tos)) [])). {
            unfold not. intros. destruct H2 as [froms [tos H2]]. inversion H2.
        }

        unfold not in HH. apply HH. clear HH.

        apply (IG_mkGraph_any_ins_all_nodes _ B _ edges l) in H.
        assert (In l (l :: nodes)). {

            simpl. auto.
        }
        apply H in H2. clear H.

        rewrite _In_labNodes_is_some_MapsTo in H2.
        destruct H2 as [fromss [toss H2]].
        exists fromss, toss.

        
        apply -> MFacts.elements_mapsto_iff in H2.
        unfold IG_mkGraph in H2.
        assert (NatMap.elements (elt:=Adj B * A * Adj B) (_insEdges edges (_insNodes (l :: nodes) IG_empty)) = []). {
            assumption.

        }
        rewrite  H in H2.
        assumption.

        
        + congruence.
Qed.
