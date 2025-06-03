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

Require Import GraphVerification.src.inductive.inductive_graph.
Require Import GraphVerification.src.inductive.inductive_graph_measure.


Require Import GraphVerification.src.relational_graph.
Require Import GraphVerification.src.relational_graph_theory.

Require Import GraphVerification.src.util.NatMap.





(* (attempt at) direct equational specifications of an IG: *)

(* Block to derive useful conversion theorem "In_labNodes_is_InMap" *)
Check NatMap.elements .


(* Notive, how In + [] is basically used as a set. Also possibly provide no duplicates proofs *) 

(* Helper lemma for converting an In (of a map) to an InA, which will eventually be turned to a NatMap.In (which has useful lemmas)  *)
Lemma _In_map_fst_InA : forall (A B: Type) (x : LNode A) (l : list (Node * (Context' A B))),
  In x (map (fun '(v, (_, l, _)) => (v, l)) l) <-> exists (froms tos : Adj B), InA (fun (e1 e2 : (Node * (Context' A B))) => NatMap.eq_key_elt e1 e2) (fst x, (froms, snd x, tos)) l.  
Proof.
  intros. induction l; simpl.
  - split; intros.
    + destruct H.
    + destruct H as [froms [tos H]]. inversion H.
  - split; intros.
    + destruct H.
      -- destruct a as [n [[froms label] tos]]. exists froms, tos. left. destruct H. simpl. reflexivity.  
      -- edestruct IHl. apply H0 in H. destruct H as [froms [tos H]]. exists froms, tos. apply InA_cons. right. assumption.
    + destruct H as [froms [tos H]]. inversion H.
      -- left. destruct a as [n [[fromss labell] toss]]. destruct x. destruct H1. simpl in H1. simpl in H3. inversion H3. rewrite H1. reflexivity.
      -- right. apply IHl. exists froms, tos. assumption.
Qed.   


(* This is the most useful one for proving other statements.
  Use it to convert from "use friendly" In- statements to "provable" NatMap.In- statements  *)
Lemma _In_labNodes_is_InMap : forall (A B : Type) (x : LNode A) (ig : IG A B),
  In x (IG_labNodes ig) <-> exists froms tos, NatMap.MapsTo (fst x) (froms, snd x, tos) ig.     
Proof.
  intros. unfold IG_labNodes.
  pose proof (MFacts.elements_mapsto_iff ig).
  symmetry.
  rewrite _In_map_fst_InA.

  split; intros.
  + destruct H0 as [fromss [toss H0]]. exists fromss, toss. destruct (H (fst x) (fromss, snd x, toss)).
    apply H1 in H0. assumption.
  + destruct H0 as [froms [tos H0]]. exists froms, tos. apply H. apply H0.
Qed.


(* Prove the same, but only for keys *)
Lemma _In_map_fst_InA' : forall (A: Type) (a : Node) (l : list (Node * A)),
  In a (map fst l) <-> exists (a0 : A), InA (fun (x el : (Node * A)) => NatMap.eq_key_elt x el) (a, a0) l.
Proof.
  intros. induction l; simpl.
  - split; intros.
    + destruct H.
    + destruct H. inversion H.
  - split; intros.
    + destruct H.
      -- exists (snd a0). left. destruct a0. destruct H. simpl. reflexivity.
      -- edestruct IHl. apply H0 in H. destruct H. exists x. apply InA_cons. right. assumption.
    + destruct H. inversion H.
      -- left. destruct a0. destruct H1. simpl in *. rewrite H1. reflexivity.
      -- right. apply IHl. exists x. assumption.
Qed.

Lemma _complicated_fst_is_fst : forall (A B : Type),
(fun x0 : NatMap.key * (Adj B * A * Adj B) => fst (let '(v, (_, l, _)) := x0 in (v, l))) = fst.
Proof.
  intros.
  apply functional_extensionality. intros. destruct x as [n [[froms l] tos]]. simpl. reflexivity.
Qed. 

(* Lemma _InA_is_In : 
  (exists a0 InA (fun x0 el => NatMap.eq_key_elt x0 el) (x, a0) (NatMap.elements ig)) <->
    NatMap.In x ig *)

Lemma _In_labNodes_is_InMap' : forall (A B : Type) (x : Node) (ig : IG A B),
  In x (map fst (IG_labNodes ig)) <-> NatMap.In x ig. 
Proof.
  intros. unfold IG_labNodes. rewrite map_map.
  rewrite _complicated_fst_is_fst.

  rewrite _In_map_fst_InA'.
  unfold NatMap.In. unfold NatMap.Raw.In0.
  split.
  - intros. destruct H. exists x0. apply MFacts.elements_mapsto_iff in H. assumption.
  - intros. destruct H. exists x0. apply MFacts.elements_mapsto_iff in H. assumption.
Qed.





(* Here start "meaningful statements" *)


(* 5 statements on inserting (helpers for mkGraph): update, insEdge, insEdges, insNode, insNodes *)
Lemma _updateEntry_does_not_change_key_set : forall (A B : Type) (node : Node) (f : Context' A B -> Context' A B) (ig : IG A B) (x : Node),
  In x (map fst (IG_labNodes (_updateEntry node f ig))) <-> In x (map fst (IG_labNodes ig)).
Proof.
  intros. unfold _updateEntry.
  destruct (NatMap.find node ig) eqn:isIn.
  - rewrite !_In_labNodes_is_InMap'. rewrite MFacts.add_in_iff.
    rewrite MFacts.in_find_iff. split.
    + intros. destruct H.
      -- rewrite <- H. rewrite isIn. unfold not. intros. discriminate H0.
      -- assumption.
    + intros. right. assumption.
  - reflexivity.
Qed.

Lemma _updAdj_does_not_change_key_set : forall (A B : Type) (adj : Adj B) (f : B -> Context' A B -> Context' A B) (ig : IG A B) (x : Node), 
  In x (map fst (IG_labNodes (_updAdj adj f ig))) <-> In x (map fst (IG_labNodes ig)).
Proof.
  intros. unfold _updAdj.
  induction adj.
  - simpl. reflexivity.
  - simpl. destruct a. rewrite _updateEntry_does_not_change_key_set. rewrite <- IHadj. reflexivity.
Qed.


(* util *)
Require Import GraphVerification.src.util.util.

Check _addSucc.
Check _addSucc 3.
Check _updateEntry.

(* This is just a lightly harder version of the 2 proofs above *)
Lemma _updateEntry_addSucc_does_not_change_lab_nodes : forall (A B : Type) (node : Node) (whose : Node) (l : B) (ig : IG A B) (x : LNode A),
  In x (IG_labNodes (_updateEntry node (_addSucc whose l) ig)) <-> In x (IG_labNodes ig).    
Proof.
  intros. unfold _updateEntry. unfold _addSucc. 
  destruct (NatMap.find node ig) eqn:isIn.
  - destruct c as [[froms label] tos]. rewrite !_In_labNodes_is_InMap. split; intros.
    + destruct H as [fromss [toss H]]. apply MFacts.add_mapsto_iff in H. destruct H.
      -- exists froms, tos. destruct H. inversion H0. subst. apply MFacts.find_mapsto_iff. assumption.
      -- firstorder.
    + firstorder. bdestruct ((fst x) =? node).
      -- subst. exists froms, ((l, whose) :: tos). apply MFacts.add_mapsto_iff. left. split.
        ++ reflexivity.
        ++ destruct x. simpl in *. apply MFacts.find_mapsto_iff in isIn. assert ((froms, label, tos) = (x0, a, x1)). {
          apply (MFacts.MapsTo_fun isIn).
          assumption.
        }
        inversion H0. firstorder.
      -- exists x0, x1. apply MFacts.add_mapsto_iff. right. split.
        ++ lia.
        ++ assumption.
  - reflexivity.
Qed.



Lemma _updAdj_addSucc_does_not_change_lab_nodes : forall (A B : Type) (node : Node) (adj : Adj B) (ig : IG A B) (x : LNode A), 
  In x (IG_labNodes (_updAdj adj (_addSucc node) ig)) <-> In x (IG_labNodes ig).
Proof.
  intros. unfold _updAdj.
  induction adj.
  - simpl. reflexivity.
  - simpl. destruct a. rewrite _updateEntry_addSucc_does_not_change_lab_nodes. rewrite <- IHadj. reflexivity.
Qed.

(* this is just a pallete- swap version of the two proofs above *)
Lemma _updateEntry_addPred_does_not_change_lab_nodes : forall (A B : Type) (node : Node) (whose : Node) (l : B) (ig : IG A B) (x : LNode A),
  In x (IG_labNodes (_updateEntry node (_addPred whose l) ig)) <-> In x (IG_labNodes ig).    
Proof.
  intros. unfold _updateEntry. unfold _addPred. 
  destruct (NatMap.find node ig) eqn:isIn.
  - destruct c as [[froms label] tos]. rewrite !_In_labNodes_is_InMap. split; intros.
    + destruct H as [fromss [toss H]]. apply MFacts.add_mapsto_iff in H. destruct H.
      -- exists froms, tos. destruct H. inversion H0. subst. apply MFacts.find_mapsto_iff. assumption.
      -- firstorder.
    + firstorder. bdestruct ((fst x) =? node).
      -- subst. exists ((l, whose) :: froms), tos. apply MFacts.add_mapsto_iff. left. split. 
        ++ reflexivity.
        ++ destruct x. simpl in *. apply MFacts.find_mapsto_iff in isIn. assert ((froms, label, tos) = (x0, a, x1)). {
          apply (MFacts.MapsTo_fun isIn).
          assumption.
        }
        inversion H0. firstorder.
      -- exists x0, x1. apply MFacts.add_mapsto_iff. right. split.
        ++ lia.
        ++ assumption.
  - reflexivity.
Qed.

Lemma _updAdj_addPred_does_not_change_lab_nodes : forall (A B : Type) (node : Node) (adj : Adj B) (ig : IG A B) (x : LNode A), 
  In x (IG_labNodes (_updAdj adj (_addPred node) ig)) <-> In x (IG_labNodes ig).
Proof.
  intros. unfold _updAdj.
  induction adj.
  - simpl. reflexivity.
  - simpl. destruct a. rewrite _updateEntry_addPred_does_not_change_lab_nodes. rewrite <- IHadj. reflexivity.
Qed.



(* This could be written in terms of match eb: match x (add x ig) = (Some x, i) *)
Lemma IG_add_adds_node : forall (A B : Type) (context : Context A B) (ig : IG A B) (x : LNode A),
  In x (IG_labNodes (IG_and context ig)) <-> let '(_, node, label, _) := context in In x ((if NatMap.mem node ig then [] else [(node, label)]) ++ IG_labNodes ig).
Proof.
  intros. simpl.
  destruct context as [[[froms node] label] tos]. unfold IG_and.
  destruct (NatMap.mem node ig) eqn:cond; simpl.
  - reflexivity.
  - rewrite _updAdj_addSucc_does_not_change_lab_nodes. rewrite _updAdj_addPred_does_not_change_lab_nodes.
    rewrite !_In_labNodes_is_InMap. 
  
  split; intros.
    + destruct H as [fromss [toss H]]. apply MFacts.add_mapsto_iff in H. destruct H.
      -- left. destruct x. destruct H. inversion H0. simpl in *. subst. reflexivity.
      -- right. destruct H. firstorder.
    + destruct H.
      -- exists froms, tos. apply MFacts.add_mapsto_iff. left. destruct x. inversion H. simpl in *. subst. auto.
      -- destruct H as [fromss [toss H]]. exists fromss, toss. apply MFacts.add_mapsto_iff. right. split.
        ++ unfold not. intros. destruct x. simpl in *. subst. assert (NatMap.In n ig). {
            firstorder.          
        } apply NatMap.mem_1 in H0. rewrite H0 in cond. discriminate cond.
        ++ assumption.
Qed.





Lemma _insNode_any_ins_node : forall (A B : Type) (node : LNode A) (ig : IG A B) (x : LNode A),
  In x (IG_labNodes (_insNode node ig)) <-> In x ((if NatMap.mem (fst node) ig then [] else [node]) ++ IG_labNodes ig).
Proof.
  intros. simpl.
  destruct node.
  pose proof (IG_add_adds_node _ B (nil, n, a, nil)).
  unfold _insNode.
  rewrite H.
  simpl.
  reflexivity.
Qed.




Lemma _mem_different_insNodes : forall (A B : Type) (n : Node) (a : A) (nodes : list (LNode A)) (ig : IG A B),
  ~ InA (fun x y : NatSet.Node * A => fst x = fst y) (n, a) nodes ->
  NatMap.mem n (_insNodes nodes ig) = NatMap.mem n ig.
Proof.
  intros. induction nodes.
  - simpl. reflexivity.
  - simpl. destruct a0. assert (~ InA (fun x y : NatSet.Node * A => fst x = fst y) (n, a) nodes). {
    firstorder.
    } apply IHnodes in H0.
    assert (n <> n0). {
      firstorder.
    }
    
    destruct (NatMap.mem n ig) eqn:HH.
    + apply MFacts.mem_in_iff. apply MFacts.mem_in_iff in H0. simpl. destruct (NatMap.mem n0 (_insNodes nodes ig)).
      -- assumption.
      -- apply MFacts.add_in_iff. right. assumption.
    + apply MFacts.not_mem_in_iff. apply MFacts.not_mem_in_iff in H0. simpl. unfold not. intros. destruct (NatMap.mem n0 (_insNodes nodes ig)).
      -- firstorder.
      -- apply MFacts.add_in_iff in H2. destruct H2.
        ++ auto.
        ++ firstorder.
Qed.



Lemma _insNodes_any_ins_all_nodes : forall (A B : Type) (nodes : list (LNode A)) (ig : IG A B) (x : LNode A),
  NoDupA (fun x y => fst x = fst y) nodes ->
  In x (IG_labNodes (_insNodes nodes ig)) <-> In x (filter (fun '(n, _) => negb (NatMap.mem n ig)) nodes ++ IG_labNodes ig).
Proof.
  intros. induction nodes.
    - simpl. reflexivity.
    - simpl. inversion H. apply IHnodes in H3. rewrite _insNode_any_ins_node. destruct a. simpl.
      apply (_mem_different_insNodes _ B _ _ _ ig) in H2.
      rewrite H2.
      destruct (NatMap.mem n ig) eqn:HH.

      + simpl. rewrite H3. reflexivity.
      + simpl. rewrite H3. reflexivity.
Qed.








(* this is just a pallete- swap version of the 4 _updateEntry  proofs further above *)

(* this is just a pallete- swap version of the 4 _updateEntry  proofs further above *)
Lemma _updateEntry_clearSucc_does_not_change_lab_nodes : forall (A B : Type) (node : Node) (whose : Node) (ig : IG A B) (x : LNode A),
  In x (IG_labNodes (_updateEntry node (_clearSucc whose) ig)) <-> In x (IG_labNodes ig).   
Proof.
  intros. unfold _updateEntry. unfold _clearSucc. 
  destruct (NatMap.find node ig) eqn:isIn.
  - destruct c as [[froms label] tos]. rewrite !_In_labNodes_is_InMap. split; intros.
    + destruct H as [fromss [toss H]]. apply MFacts.add_mapsto_iff in H. destruct H.
      -- exists froms, tos. destruct H. inversion H0. subst. apply MFacts.find_mapsto_iff. assumption.
      -- firstorder.
    + firstorder. bdestruct ((fst x) =? node).
      -- subst. exists froms, (filter (fun '(_, n) => negb (n =? whose)) tos). apply MFacts.add_mapsto_iff. left. split. 
        ++ reflexivity.
        ++ destruct x. simpl in *. apply MFacts.find_mapsto_iff in isIn. assert ((froms, label, tos) = (x0, a, x1)). {
          apply (MFacts.MapsTo_fun isIn).
          assumption.
        }
        inversion H0. subst. reflexivity.
      -- exists x0, x1. apply MFacts.add_mapsto_iff. right. split.
        ++ lia.
        ++ assumption.
  - reflexivity.
Qed.


Lemma _updAdj_filter_clearSucc_does_not_change_lab_nodes : forall (A B : Type) (node : Node) (froms : Adj B)  (ig : IG A B) (x : LNode A),  
  In x (IG_labNodes
    (_updAdj (filter (fun '(_, n) => negb (n =? node)) froms) (fun (_ : B) (y : Context' A B) => _clearSucc node y)
  ig)) <-> In x (IG_labNodes ig).
Proof.
  intros. unfold _updAdj.
  induction froms.
  - simpl. reflexivity.
  - simpl. destruct a. bdestruct (n =? node).
    + simpl. assumption.
    +  simpl. rewrite _updateEntry_clearSucc_does_not_change_lab_nodes. rewrite <- IHfroms. reflexivity.
Qed.



Lemma _updateEntry_clearPred_does_not_change_lab_nodes : forall (A B : Type) (node : Node) (whose : Node) (ig : IG A B) (x : LNode A),
  In x (IG_labNodes (_updateEntry node (_clearPred whose) ig)) <-> In x (IG_labNodes ig).     
Proof.
  intros. unfold _updateEntry. unfold _clearPred. 
  destruct (NatMap.find node ig) eqn:isIn.
  - destruct c as [[froms label] tos]. rewrite !_In_labNodes_is_InMap. split; intros.
    + destruct H as [fromss [toss H]]. apply MFacts.add_mapsto_iff in H. destruct H.
      -- exists froms, tos. destruct H. inversion H0. subst. apply MFacts.find_mapsto_iff. assumption.
      -- firstorder.
    + firstorder. bdestruct ((fst x) =? node).
      -- subst. exists  (filter (fun '(_, n) => negb (n =? whose)) froms), tos. apply MFacts.add_mapsto_iff. left. split. 
        ++ reflexivity.
        ++ destruct x. simpl in *. apply MFacts.find_mapsto_iff in isIn. assert ((froms, label, tos) = (x0, a, x1)). {
          apply (MFacts.MapsTo_fun isIn).
          assumption.
        }
        inversion H0. subst. reflexivity.
      -- exists x0, x1. apply MFacts.add_mapsto_iff. right. split.
        ++ lia.
        ++ assumption.
  - reflexivity.
Qed.


Lemma _updAdj_filter_clearPred_does_not_change_lab_nodes : forall (A B : Type) (node : Node) (tos : Adj B)  (ig : IG A B) (x : LNode A), 
  In x (IG_labNodes
    (_updAdj (filter (fun '(_, n) => negb (n =? node)) tos) (fun (_ : B) (y : Context' A B) => _clearPred node y)
  ig)) <-> In x (IG_labNodes ig).
Proof.
  intros. unfold _updAdj.
  induction tos.
  - simpl. reflexivity.
  - simpl. destruct a. bdestruct (n =? node).
    + simpl. assumption.
    +  simpl. rewrite _updateEntry_clearPred_does_not_change_lab_nodes. rewrite <- IHtos. reflexivity.
Qed.





Lemma IG_match_removes_node : forall (A B : Type) (query : Node) (mContext : MContext A B) (ig rest : IG A B),
  IG_match query ig = (mContext, rest) -> 
  (forall label, not (In (query, label) (IG_labNodes rest))).
Proof.
  intros. unfold not. intros.
  unfold IG_match in H. destruct (NatMap.find query ig) eqn:HH.
  - unfold _cleanSplit in H. destruct c as [[fromss l] toss]. inversion H. clear H H2. rewrite <- H3 in H0. clear H3.
    apply _updAdj_filter_clearPred_does_not_change_lab_nodes in H0.
    apply _updAdj_filter_clearSucc_does_not_change_lab_nodes in H0.

    apply _In_labNodes_is_InMap in H0. destruct H0 as [fromsss [tosss H0]]. simpl in H0.
    apply MFacts.remove_mapsto_iff in H0. destruct H0.
    destruct H. reflexivity.
  
  - inversion H. subst. apply MFacts.not_find_in_iff in HH. apply _In_labNodes_is_InMap in H0.
    assert (NatMap.In query rest). {
      firstorder.
    }
    auto.
Qed.


(* TODO: think of this being a permutation, maybe its too hard *)
Lemma IG_match_just_removes_node : forall (A B : Type) (query hit : Node) (label : A) (ig rest : IG A B) (froms tos : Adj B) (x : LNode A),
  IG_match query ig = (Some (froms, hit, label, tos), rest) -> 
  In x (IG_labNodes ig) <-> In x ((hit, label) :: IG_labNodes rest). 
Proof.
  intros. simpl.
  unfold IG_match in H. destruct (NatMap.find query ig) eqn:HH.
  - unfold _cleanSplit in H. destruct c as [[fromss l] toss]. inversion H. subst.
    split; intros.
    + bdestruct (hit =? fst x).
      -- destruct x.  subst. left. f_equal. apply _In_labNodes_is_InMap in H0. simpl in H0. firstorder. apply MFacts.find_mapsto_iff in HH.
        assert ((fromss, label, tos) = (x, a, x0)). {
          apply (MFacts.MapsTo_fun HH H0).
        }
        inversion H1. reflexivity.
      -- right. apply _updAdj_filter_clearPred_does_not_change_lab_nodes. apply _updAdj_filter_clearSucc_does_not_change_lab_nodes.
        apply _In_labNodes_is_InMap. apply _In_labNodes_is_InMap in H0. firstorder. exists x0, x1.
        apply MFacts.remove_mapsto_iff. split.
        ++ assumption.
        ++ assumption.
    + destruct H0.
      -- subst. apply MFacts.find_mapsto_iff in HH. apply _In_labNodes_is_InMap. exists fromss, tos. assumption.
      -- apply _updAdj_filter_clearPred_does_not_change_lab_nodes in H0. apply _updAdj_filter_clearSucc_does_not_change_lab_nodes in H0.
        apply _In_labNodes_is_InMap in H0. apply _In_labNodes_is_InMap. firstorder. exists x0, x1. apply MFacts.remove_mapsto_iff in H0.
        destruct H0. assumption.
 

  - inversion H.
Qed.



Lemma IG_match_returns_valid_neighbours : forall (A B : Type) (query : Node) (ig i : IG A B) (c : Context A B) (n : Node),
    let '(froms, hit, label, tos) := c in
    IG_match query ig = (Some (froms, hit, label, tos), i) ->
    (In n (map snd froms) \/ In n (map snd tos)) ->
    In n (map fst (IG_labNodes i)).
Proof.
Admitted.




Lemma _insEdge_does_not_add_node : forall (A B : Type) (edge : LEdge B) (ig : IG A B) (x : LNode A),
  In x (IG_labNodes (_insEdge edge ig)) <-> In x (IG_labNodes ig).
Proof.
  intros. unfold _insEdge. destruct edge as [[from to] label].
  destruct (IG_match from ig) eqn:HH.
  destruct m as [[[[froms n] l] tos] | ].
  - rewrite IG_add_adds_node. destruct (NatMap.mem from i) eqn:HHH.
    + exfalso. apply IG_match_returns_node in HH as HHHH. subst.
      apply  MFacts.mem_in_iff in HHH.
      
      assert (exists c, NatMap.MapsTo n c i). {
        firstorder.
      }
      destruct H as [[[fromss node] toss] H].

      assert (In (n, node) (IG_labNodes i)). {
        apply _In_labNodes_is_InMap. firstorder.
      }

      eapply IG_match_removes_node in HH.
      unfold not in HH. apply HH. apply H0.


    + simpl. apply IG_match_returns_node in HH as HHHH. subst. apply (IG_match_just_removes_node _ _ _ _ _ _ _ _ _ x) in HH. rewrite HH. simpl. reflexivity.
  - reflexivity.
Qed.











Lemma _insEdges_does_not_add_nodes : forall (A B : Type) (edges : list (LEdge B)) (ig : IG A B) (x : LNode A), 
  In x (IG_labNodes (_insEdges edges ig)) <-> In x (IG_labNodes ig).
Proof.
  intros. simpl. induction edges.
  - simpl. reflexivity.
  - simpl. rewrite _insEdge_does_not_add_node. rewrite IHedges. reflexivity.
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

(* "big" statement: *)
Theorem IG_mkGraph_any_ins_all_nodes : forall (A B : Type) (nodes : list (LNode A)) (edges : list (LEdge B)) (x : LNode A),
  NoDupA (fun x y => fst x = fst y) nodes ->
  In x (IG_labNodes (IG_mkGraph nodes edges)) <-> In x nodes.
Proof.
  intros. unfold IG_mkGraph. rewrite _insEdges_does_not_add_nodes. rewrite _insNodes_any_ins_all_nodes.
  - rewrite app_nil_r. simpl. rewrite _filter_identity. reflexivity.
  - assumption.
Qed.


Theorem IG_empty_isEmpty : forall (A B : Type), IG_isEmpty (@IG_empty A B) = true.
Proof.
  compute. reflexivity.
Qed.

Theorem IG_labNodes_empty_nil : forall (A B : Type), IG_labNodes (@IG_empty A B) = [].
Proof.
  compute. reflexivity.
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


      rewrite _In_labNodes_is_InMap in H2.
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



Theorem IG_matsh_empty_is_nothing : forall (A B : Type) (node : Node),
  IG_match node (@IG_empty A B) = (None, IG_empty).   
Proof.
  intros. compute. reflexivity.
Qed.


Theorem IG_spec4 : forall (A B : Type) (node : Node) (nodes : list (LNode A)) (edges : list (LEdge B)), 
  In node (map fst nodes) -> exists froms tos, IG_match node (IG_mkGraph nodes edges) =
  (Some (froms, tos), IG_mkGraph (filter (fun '(n, _) => negb (node =? n)) nodes) (filter (fun '(from, to, _) => negb ((from =? node) || (to =? node))) edges)).
(* This is not even a complete specification and it looks like a hard one to prove... *)
Proof.
  intros.
  
Admitted.


Theorem IG_spec5 : forall (A B : Type) (node : Node) (nodes : list (LNode A)) (edges : list (LEdge B)), 
  not (In node (map fst nodes)) -> IG_match node (IG_mkGraph nodes edges) = (None, IG_mkGraph nodes edges).
Proof.
Admitted.





(* Start proving some properties of DFS *)

Lemma _In_map_fst_exists_second : forall (A B: Type) (a : A) (l : list (A * B)),
In a (map fst l) <-> exists second, In (a, second) l.
Proof.
  intros. induction l; simpl.
  - firstorder.
  - destruct a0. split; intros.
    + destruct H.
      -- exists b. left. subst. auto.
      -- firstorder.
    + destruct H. destruct H.
      -- left. inversion H. auto.
      -- right. apply IHl. exists x. assumption.
Qed.





(* here start the theorems on match decreasing the cardinality: *)




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



