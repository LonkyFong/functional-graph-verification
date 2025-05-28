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


Require Import MyProject.project.util.NatSet.

Require Import MyProject.project.inductive.inductive_graph.
Require Import MyProject.project.inductive.inductive_graph_to_RG.

Require Import MyProject.project.relational_graph.
Require Import MyProject.project.relational_graph_theory.

Require Import MyProject.project.util.NatMap.

(* This file shows that I== is an equivalence and attempts at "direct equational specification" of IG s  *)


(* Section to make rewrite work with IG_equiv *)
(* This proof is based on === being an equivalence relation *)
Instance IG_Equivalence {A B : Type} : Equivalence (@IG_equiv A B).
Proof.
  G_derived_equivalence_prover nat unit (@ IG_to_RG A B).  
Qed.


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
  pose proof (WF.elements_mapsto_iff ig).
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


Lemma _In_labNodes_is_InMap' : forall (A B : Type) (x : Node) (ig : IG A B),
  In x (map fst (IG_labNodes ig)) <-> NatMap.In x ig. 
Proof.
  intros. unfold IG_labNodes. rewrite map_map.
  rewrite _complicated_fst_is_fst.

  apply _In_map_fst_InA'.
Qed.





(* Here start "meaningful statements" *)


(* 5 statements on inserting (helpers for mkGraph): update, insEdge, insEdges, insNode, insNodes *)
Lemma _updateEntry_does_not_change_key_set : forall (A B : Type) (node : Node) (f : Context' A B -> Context' A B) (ig : IG A B) (x : Node),
  In x (map fst (IG_labNodes (_updateEntry node f ig))) <-> In x (map fst (IG_labNodes ig)).
Proof.
  intros. unfold _updateEntry.
  destruct (NatMap.find node ig) eqn:isIn.
  - rewrite !_In_labNodes_is_InMap'. rewrite WF.add_in_iff.
    rewrite WF.in_find_iff. split.
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
Require Import MyProject.project.util.util.

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
    + destruct H as [fromss [toss H]]. apply WF.add_mapsto_iff in H. destruct H.
      -- exists froms, tos. destruct H. inversion H0. subst. apply WF.find_mapsto_iff. assumption.
      -- firstorder.
    + firstorder. bdestruct ((fst x) =? node).
      -- subst. exists froms, ((l, whose) :: tos). apply WF.add_mapsto_iff. left. split.
        ++ reflexivity.
        ++ destruct x. simpl in *. apply WF.find_mapsto_iff in isIn. assert ((froms, label, tos) = (x0, a, x1)). {
          apply (WF.MapsTo_fun isIn).
          assumption.
        }
        inversion H0. firstorder.
      -- exists x0, x1. apply WF.add_mapsto_iff. right. split.
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
    + destruct H as [fromss [toss H]]. apply WF.add_mapsto_iff in H. destruct H.
      -- exists froms, tos. destruct H. inversion H0. subst. apply WF.find_mapsto_iff. assumption.
      -- firstorder.
    + firstorder. bdestruct ((fst x) =? node).
      -- subst. exists ((l, whose) :: froms), tos. apply WF.add_mapsto_iff. left. split. 
        ++ reflexivity.
        ++ destruct x. simpl in *. apply WF.find_mapsto_iff in isIn. assert ((froms, label, tos) = (x0, a, x1)). {
          apply (WF.MapsTo_fun isIn).
          assumption.
        }
        inversion H0. firstorder.
      -- exists x0, x1. apply WF.add_mapsto_iff. right. split.
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


Lemma IG_add_adds_node : forall (A B : Type) (context : Context A B) (ig : IG A B) (x : LNode A),
  In x (IG_labNodes (add context ig)) <-> let '(_, node, label, _) := context in In x ((if NatMap.mem node ig then [] else [(node, label)]) ++ IG_labNodes ig).
Proof.
  intros. simpl.
  destruct context as [[[froms node] label] tos]. unfold add.
  destruct (NatMap.mem node ig) eqn:cond; simpl.
  - reflexivity.
  - rewrite _updAdj_addSucc_does_not_change_lab_nodes. rewrite _updAdj_addPred_does_not_change_lab_nodes.
    rewrite !_In_labNodes_is_InMap. 
  
  split; intros.
    + destruct H as [fromss [toss H]]. apply WF.add_mapsto_iff in H. destruct H.
      -- left. destruct x. destruct H. inversion H0. simpl in *. subst. reflexivity.
      -- right. destruct H. firstorder.
    + destruct H.
      -- exists froms, tos. apply WF.add_mapsto_iff. left. destruct x. inversion H. simpl in *. subst. auto.
      -- destruct H as [fromss [toss H]]. exists fromss, toss. apply WF.add_mapsto_iff. right. split.
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
    + apply WF.mem_in_iff. apply WF.mem_in_iff in H0. simpl. destruct (NatMap.mem n0 (_insNodes nodes ig)).
      -- assumption.
      -- apply WF.add_in_iff. right. assumption.
    + apply WF.not_mem_in_iff. apply WF.not_mem_in_iff in H0. simpl. unfold not. intros. destruct (NatMap.mem n0 (_insNodes nodes ig)).
      -- firstorder.
      -- apply WF.add_in_iff in H2. destruct H2.
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




(* this is just a pallete- swap version of the 4 _updateEntry  proofs further above *)

(* this is just a pallete- swap version of the 4 _updateEntry  proofs further above *)
Lemma _updateEntry_clearSucc_does_not_change_lab_nodes : forall (A B : Type) (node : Node) (whose : Node) (ig : IG A B) (x : LNode A),
  In x (IG_labNodes (_updateEntry node (_clearSucc whose) ig)) <-> In x (IG_labNodes ig).   
Proof.
  intros. unfold _updateEntry. unfold _clearSucc. 
  destruct (NatMap.find node ig) eqn:isIn.
  - destruct c as [[froms label] tos]. rewrite !_In_labNodes_is_InMap. split; intros.
    + destruct H as [fromss [toss H]]. apply WF.add_mapsto_iff in H. destruct H.
      -- exists froms, tos. destruct H. inversion H0. subst. apply WF.find_mapsto_iff. assumption.
      -- firstorder.
    + firstorder. bdestruct ((fst x) =? node).
      -- subst. exists froms, (filter (fun '(_, n) => negb (n =? whose)) tos). apply WF.add_mapsto_iff. left. split. 
        ++ reflexivity.
        ++ destruct x. simpl in *. apply WF.find_mapsto_iff in isIn. assert ((froms, label, tos) = (x0, a, x1)). {
          apply (WF.MapsTo_fun isIn).
          assumption.
        }
        inversion H0. subst. reflexivity.
      -- exists x0, x1. apply WF.add_mapsto_iff. right. split.
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
    + destruct H as [fromss [toss H]]. apply WF.add_mapsto_iff in H. destruct H.
      -- exists froms, tos. destruct H. inversion H0. subst. apply WF.find_mapsto_iff. assumption.
      -- firstorder.
    + firstorder. bdestruct ((fst x) =? node).
      -- subst. exists  (filter (fun '(_, n) => negb (n =? whose)) froms), tos. apply WF.add_mapsto_iff. left. split. 
        ++ reflexivity.
        ++ destruct x. simpl in *. apply WF.find_mapsto_iff in isIn. assert ((froms, label, tos) = (x0, a, x1)). {
          apply (WF.MapsTo_fun isIn).
          assumption.
        }
        inversion H0. subst. reflexivity.
      -- exists x0, x1. apply WF.add_mapsto_iff. right. split.
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
    apply WF.remove_mapsto_iff in H0. destruct H0.
    destruct H. reflexivity.
  
  - inversion H. subst. apply WF.not_find_in_iff in HH. apply _In_labNodes_is_InMap in H0.
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
      -- destruct x.  subst. left. f_equal. apply _In_labNodes_is_InMap in H0. simpl in H0. firstorder. apply WF.find_mapsto_iff in HH.
        assert ((fromss, label, tos) = (x, a, x0)). {
          apply (WF.MapsTo_fun HH H0).
        }
        inversion H1. reflexivity.
      -- right. apply _updAdj_filter_clearPred_does_not_change_lab_nodes. apply _updAdj_filter_clearSucc_does_not_change_lab_nodes.
        apply _In_labNodes_is_InMap. apply _In_labNodes_is_InMap in H0. firstorder. exists x0, x1.
        apply WF.remove_mapsto_iff. split.
        ++ assumption.
        ++ assumption.
    + destruct H0.
      -- subst. apply WF.find_mapsto_iff in HH. apply _In_labNodes_is_InMap. exists fromss, tos. assumption.
      -- apply _updAdj_filter_clearPred_does_not_change_lab_nodes in H0. apply _updAdj_filter_clearSucc_does_not_change_lab_nodes in H0.
        apply _In_labNodes_is_InMap in H0. apply _In_labNodes_is_InMap. firstorder. exists x0, x1. apply WF.remove_mapsto_iff in H0.
        destruct H0. assumption.
 

  - inversion H.
Qed.




  
  
  


Lemma _insEdge_does_not_add_node : forall (A B : Type) (edge : LEdge B) (ig : IG A B) (x : LNode A),
  In x (IG_labNodes (_insEdge edge ig)) <-> In x (IG_labNodes ig).
Proof.
  intros. unfold _insEdge. destruct edge as [[from to] label].
  destruct (IG_match from ig) eqn:HH.
  destruct m as [[[[froms n] l] tos] | ].
  - rewrite IG_add_adds_node. destruct (NatMap.mem from i) eqn:HHH.
    + exfalso. apply IG_match_returns_node in HH as HHHH. subst.
      apply  WF.mem_in_iff in HHH.
      
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
  intros. unfold not. rewrite WF.is_empty_iff. destruct (NatMap.is_empty (elt:=A) m) eqn:cond.
  - firstorder. congruence.
  - firstorder. congruence.
Qed.

(* Think about enforcing non-emptiness of the list with (x::xs) *)
Theorem  IG_non_empty_isEmpty_false : forall (A B : Type) (nodes : list (LNode A)) (edges : list (LEdge B)),
  NoDupA (fun x y => fst x = fst y) nodes ->
  length nodes <> 0 <-> IG_isEmpty ((IG_mkGraph nodes edges)) = false.
Proof.
  intros. unfold IG_isEmpty. rewrite <- _not_NatMap_Empty_is_empty_false. unfold not.
  destruct nodes; simpl; unfold IG_mkGraph.
  - firstorder.
    apply H0.
    apply WP.elements_Empty.

    rewrite _insEdges_on_empty_is_empty. compute. reflexivity.
  - firstorder.
    + apply WP.elements_Empty in H1.
      assert (HH : not (exists (froms tos : Adj B), InA (fun (e1 e2 : (Node * (Context' A B))) => NatMap.eq_key_elt e1 e2) (fst l, (froms, snd l, tos)) [])). {
        unfold not. intros. destruct H2 as [froms [tos H2]]. inversion H2.
      }

      unfold not in HH. apply HH. clear HH.

      apply (IG_mkGraph_any_ins_all_nodes _ B _ edges l) in H.
      assert (In l (l :: nodes)). {
        firstorder.
      }
      apply H in H2. clear H.


      rewrite _In_labNodes_is_InMap in H2.
      destruct H2 as [fromss [toss H2]].
      exists fromss, toss.

      
      apply -> WF.elements_mapsto_iff in H2.
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




Definition _nodeAmount {A B : Type} (ig : IG A B) : nat :=
  NatMap.cardinal ig.



(* here start the theorems on match decreasing the cardinality: *)

(* Copy from inductive graph *)
Lemma _IG_updateEntry_does_not_change_cardinality : forall {A B : Type} (node : Node) (f : Context' A B -> Context' A B) (ig : IG A B), 
    NatMap.cardinal (_updateEntry node f ig) = NatMap.cardinal ig.
Proof.
  intros. unfold _updateEntry.

  destruct (NatMap.find node ig) eqn:split.
  - 

  assert (NatMap.Equal ig (NatMap.add node c ig)). { 
      apply WF.find_mapsto_iff in split.

    apply WF.Equal_mapsto_iff.
    split; intros.
    - apply WF.add_mapsto_iff.
       bdestruct (node =? k).
      + subst. left. split.
      -- reflexivity.
      -- apply WF.find_mapsto_iff in split. apply WF.find_mapsto_iff in H. rewrite H in split. inversion split. reflexivity.
      + right. split.
      -- assumption.
      -- assumption.
    - apply WF.add_mapsto_iff in H. destruct H.
      + destruct H. subst. assumption.
      + destruct H. assumption.
  }
  rewrite H at 2.
  apply _add_value_does_not_matter_for_cardinality.
  - reflexivity.

Qed.


(* Copy from inductive graph *)
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

(* Copy from inductive graph *)
Lemma _map_find_some_remove_lowers_cardinality : forall {A : Type} (key : Node) (map : NatMap.t A),
  (exists x, NatMap.find key map = Some x) -> (NatMap.cardinal map = S (NatMap.cardinal (NatMap.remove key map))).
Proof.
  
  intros.
  pose proof WP.cardinal_2.
  destruct H eqn:hu.
  assert (~ NatMap.In key (NatMap.remove key map)). {
    unfold not. intros.
    apply WF.remove_in_iff in H1.
    destruct H1.
    destruct H1.
    reflexivity.

  }
  apply (H0 _ _ map _ x) in H1.
  - rewrite <- H1. reflexivity.
  - unfold WP.Add. 
  
  
  
  unfold WP.Add. intros. bdestruct (y =? key).
  + rewrite H2. rewrite e. assert (key = key). {
    reflexivity.
  }  pose proof WF.add_eq_o. apply (H4 A (NatMap.remove (elt:=A) key map) _ _ x) in H3. rewrite H3. reflexivity.
  + pose proof WF.add_neq_o. assert (key <> y). {lia. } apply (H3 A (NatMap.remove (elt:=A) key map) _ _ x) in H4. rewrite H4.
    pose proof WF.remove_neq_o. assert (key <> y). {lia. }  apply (H5 A map _ _) in H6. rewrite H6. reflexivity.
  
Defined.

(* Copy of IG_dft'terminates1 *)
Theorem _IG_match_decreases_nodeAmount : forall (A B : Type) (n : Node) (c : Context A B) (ig rest : IG A B),
  IG_match n ig = (Some c, rest) -> _nodeAmount rest < _nodeAmount ig.
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
      apply _map_find_some_remove_lowers_cardinality.
      exists (fromss, labell, toss).
      apply split.
      - inversion H.
      

    }
    unfold _nodeAmount.
    lia.
Qed.


Theorem _IG_matchAny_decreases_nodeAmount : forall (A B : Type) (c : Context A B) (ig rest : IG A B),
  IG_matchAny ig = (Some c, rest) -> _nodeAmount rest < _nodeAmount ig.
Proof.
  intros. unfold IG_matchAny in H. destruct (IG_labNodes ig) eqn:labNodes.
  - inversion H.
  - apply _IG_match_decreases_nodeAmount in H. assumption.
Qed.





(* Alternative way to prove _IG_match_decreases_nodeAmount *)
Lemma IG_labNodes_len_cardinal : forall (A B : Type) (ig : IG A B),
  NatMap.cardinal ig = length (IG_labNodes ig).
Proof.
  intros. unfold IG_labNodes. rewrite map_length.
  rewrite NatMap.cardinal_1. reflexivity. 
Qed.

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
  IG_match n ig = (Some c, rest) -> _nodeAmount rest < _nodeAmount ig.
Proof.
  intros. destruct c as [[[froms node] label] tos]. apply IG_match_returns_node in H as s. subst.
  assert (NatMap.cardinal ig = S (NatMap.cardinal rest)). {
    rewrite !IG_labNodes_len_cardinal.
    apply IG_match_labNodes_permuation in H.
    apply _lists_diff_by_one in H.
    - assumption.
    - apply (node, label).
  }
  unfold _nodeAmount.
  lia.
Qed.






Function remove_nodes (nodes : list nat) {wf (fun (x y : list nat) => lt (length x) (length y)) nodes} : list nat :=
  match nodes with
  | [] => []
  | n :: ns => if n =? 420 then remove_nodes ns else n :: remove_nodes ns
  end.
Proof.
  - intros. firstorder.
  - intros. firstorder.
  - apply well_founded_ltof.
Defined.

Lemma remove_nodes_is_incl : forall (nodes : list nat),
  incl (remove_nodes nodes) nodes.
Proof.
  apply (well_founded_induction
          (well_founded_ltof _ (@length nat))). 
  intros.

  unfold incl. intros. rewrite remove_nodes_equation in H0. destruct x.
  - assumption.
  - specialize (H x). simpl. destruct (n =? 420).
    + unfold ltof in H.
    assert ( length x < length (n :: x)). {
      firstorder.
    } specialize (H H1). unfold incl in H. specialize (H a). apply H in H0. right. assumption.
    + simpl in H0. destruct H0.
      -- left. auto.
      -- right. unfold ltof in H.
        assert ( length x < length (n :: x)). {
          firstorder.
        } specialize (H H1). unfold incl in H. specialize (H a). apply H in H0. assumption.
Qed.











  

Lemma always_empty_is_empty : forall (A : Type) (l : list A),
  match l with
  | [] | _ => (@nil A)
  end = [].
Proof.
  intros. destruct l; reflexivity.
Qed.

Check well_founded_induction.
Print well_founded.
Print Acc.

Check well_founded_ltof.
Check well_founded.
Check ltof.


(* (nodesIg : list Node * IG A B) {wf (lex_prodDfs A B) nodesIg} *)

(* TODO: define that IG equivalence yields the same resulsts on most operations,
such that it is possible to rewrite using them *)

Require Import Coq.Relations.Relation_Operators.


(* Definition  *)
Theorem IG_dfs'_returns_only_nodes : forall (A B : Type) (nodesIg : list NatSet.Node * IG A B),
  let '(nodes, ig) := nodesIg in
  incl (IG_dfs'caller nodes ig) (map fst (IG_labNodes ig)). 
Proof.
  intros A B. (* Maybe the l needs to stay general in the induction hypothesis....*)
  apply (well_founded_induction
           (wf_lex_prodDfs A B)).  (* induction nodes. *)
  
  intros nodesIG IH.
  destruct nodesIG as [nodes ig].

  unfold incl in *. intros.
  unfold IG_dfs'caller in H. rewrite IG_dfs'_equation in H.
  destruct nodes.
  - apply in_nil in H. destruct H.
  - destruct (IG_isEmpty ig) eqn:em.
    + apply in_nil in H. destruct H.
    + destruct (IG_match n ig) eqn:mat.
      destruct m (*eqn:mm*).
      -- simpl in *.
          destruct H.
          (* Continue here: *)
        ++ destruct c as [[[froms node] label] tos]. 
            apply IG_match_returns_node in mat as mmmm.
            subst.

          
          eapply IG_match_just_removes_node in mat.
          apply _In_map_fst_exists_second.
          exists label.
          apply mat.
          simpl. left. reflexivity.

        ++ destruct c as [[[froms node] label] tos].
            specialize (IH (suc (froms, node, label, tos) ++ nodes, i)).
            assert (lex_prodDfs A B (suc (froms, node, label, tos) ++ nodes, i) (n :: nodes, ig)). {
              unfold lex_prodDfs. unfold lex_dProdDfs. 
              unfold prodTodPairDfs.
              simpl.
              apply left_lex.
              apply _IG_match_decreases_nodeAmount in mat.
              unfold _nodeAmount in mat.
              assumption.
            }
            specialize (IH H0).
            apply IH in H.

            rewrite _In_map_fst_exists_second in H.
            destruct H.
            rewrite _In_map_fst_exists_second.
            exists x.

            pose proof IG_match_just_removes_node.


            specialize (H1 _ _ _ _ _ _ _ _ _ (a, x) mat).
            apply H1.
            simpl.
            right. assumption.
      -- unfold IG_match in mat. destruct (NatMap.find n ig) eqn:HH.
        ++ destruct (_cleanSplit n c (NatMap.remove n ig)) eqn:split0. inversion mat.
        ++ (*i * ig*) inversion mat. subst.
            specialize (IH (nodes, i)).
            assert (lex_prodDfs A B (nodes, i) (n :: nodes, i)). {
              unfold lex_prodDfs. unfold lex_dProdDfs. 
              unfold prodTodPairDfs.
              simpl.
              apply right_lex.
              auto.
            } specialize (IH H0). firstorder.

Qed.











(* Following this website: *)
(* https://sharmaeklavya2.github.io/theoremdep/nodes/graph-theory/dfs/dfs.html *)






Theorem IG_dfs'_no_duplicates : forall (A B : Type) (nodesIg : list NatSet.Node * IG A B),
  let '(nodes, ig) := nodesIg in
  NoDup (IG_dfs'caller nodes ig).
Proof.
  intros A B. 
  apply (well_founded_induction
          (wf_lex_prodDfs A B)).  (* induction nodes. *)
  intros nodesIG IH.
  destruct nodesIG as [nodes ig].

  unfold IG_dfs'caller. rewrite IG_dfs'_equation. destruct nodes.
    - apply NoDup_nil.
    - destruct (IG_isEmpty ig) eqn:igEmpty.
      + apply NoDup_nil.
      + destruct (IG_match n ig) eqn:mat.
         destruct m eqn:mm.
         -- apply NoDup_cons.
            ++ pose proof IG_dfs'_returns_only_nodes.
              unfold incl in H. unfold not. intros. unfold IG_dfs'caller in H.
              specialize (H _ _ (suc c ++ nodes, i) _ H0). apply _In_map_fst_exists_second in H. destruct H.
             eapply IG_match_removes_node in mat.
             apply mat in H.
             apply H.

            ++ specialize (IH (suc c ++ nodes, i)).
                assert (lex_prodDfs A B (suc c ++ nodes, i) (n :: nodes, ig)). {
                  unfold lex_prodDfs. unfold lex_dProdDfs. 
                  unfold prodTodPairDfs.
                  simpl.
                  apply left_lex.
                  apply _IG_match_decreases_nodeAmount in mat.
                  unfold _nodeAmount in mat.
                  assumption.
                }
                specialize (IH H).
                apply IH.
        --  apply IG_match_none_returns_graph in mat. subst.
            specialize (IH (nodes, i)).
            assert (lex_prodDfs A B (nodes, i) (n :: nodes, i)). {
              unfold lex_prodDfs. unfold lex_dProdDfs. 
              unfold prodTodPairDfs.
              simpl.
              apply right_lex.
              auto.
            }
            specialize (IH H).
            apply IH.
Qed.
            



(* I nned to show that the remainder of the graph , does not have a anymore *) 














Definition RG_union {A B : Type} (rg1 rg2 : RG A B) : RG A B.
Proof.
    refine {|
        RG_nodes := fun a => rg1.(RG_nodes) a \/ rg2.(RG_nodes) a;
        RG_edges := fun a1 a2 l => rg1.(RG_edges) a1 a2 l \/ rg2.(RG_edges) a1 a2 l;
        RG_valid := _
    |}.
    RG_valid_prover_withs rg1 rg2.
Defined.

(* THis could eb neatened up *)
Lemma RG_union_equiv_if_both_equiv : forall {A B : Type} (rg1 rg2 rg3 rg4 : RG A B),
  (rg1 === rg2) -> (rg3 === rg4) -> (RG_union rg1 rg3 === RG_union rg2 rg4).
Proof.
  intros.
  firstorder.
Qed.




Lemma RG_transpose_distributes_over_extendByContext : forall {A B : Type} (c : Context A B) (rg : RG_unlE nat),
  RG_transpose (_extendByContext c rg) === RG_union (RG_transpose (_extendByContext c RG_empty)) (RG_transpose rg).
Proof.
  intros.
  firstorder.
  - simpl. unfold RG_transpose in H. simpl in H. destruct c as [[[froms node] label] tos]. unfold _extendByContext in H. simpl in H. firstorder.
  - simpl. unfold RG_transpose in H. simpl in H. destruct c as [[[froms node] label] tos]. unfold _extendByContext in H. simpl in H. firstorder.
  - unfold RG_transpose in H. simpl in H. destruct c as [[[froms node] label] tos]. unfold _extendByContext in H. simpl in H. firstorder.
  - unfold RG_transpose in H. simpl in H. destruct c as [[[froms node] label] tos]. unfold _extendByContext in H. simpl in H. firstorder.
  - destruct c as [[[froms node] label] tos]. unfold RG_transpose in H. simpl in H. unfold _extendByContext in H. simpl in H. firstorder.
  - destruct c as [[[froms node] label] tos]. unfold RG_transpose in H. simpl in H. unfold _extendByContext in H. simpl in H. firstorder.
Qed.


Definition _add_c_is_safe {A B : Type} (c : Context A B) (ig : IG A B) :=
  IG_matchAny ig = (Some c, ig).

  


Lemma IG_to_RG_distributes_over_add : forall {A B : Type} (c : Context A B) (ig : IG A B),
  (* _add_c_is_safe c ig -> *)
  IG_to_RG (add c ig) === RG_union ((_extendByContext c RG_empty)) (IG_to_RG ig).
Proof.
Admitted.





(* Showing properties about transpose: *)

Theorem IG_transpose_is_RG : forall (A B : Type) (ig : IG A B),
    IG_to_RG (IG_grev ig) === RG_transpose (IG_to_RG ig). 
Proof.
  intros A B.
      apply (well_founded_induction
           (well_founded_ltof _ _nodeAmount)).
    intros ig IH.
    unfold IG_grev. unfold IG_gmap. unfold IG_to_RG at 2. rewrite !IG_ufold_equation. destruct (IG_matchAny ig) eqn:mat.
    destruct m eqn:mm.
    - specialize (IH i). assert (ltof (IG A B) _nodeAmount i ig). {
      unfold ltof.
      apply _IG_matchAny_decreases_nodeAmount in mat.
      assumption.
      }
      specialize (IH H). clear H.
      rewrite RG_transpose_distributes_over_extendByContext.
      (* RHS is now "ready" for IH *)
      
      destruct c as [[[froms node] label] tos].
      
      rewrite IG_to_RG_distributes_over_add.
      apply RG_union_equiv_if_both_equiv.
        + clear mat mm IH. firstorder.
        + apply IH.
    - clear mat mm IH. unfold IG_to_RG. rewrite IG_ufold_equation. simpl. unfold RG_transpose. firstorder. 

Qed.

















(* 
(* Stuff for the vaolidity checker *)

Definition set_from_list (l : list node) : option NatSet.t :=
  fold_right (fun (k : node) (acc : option NatSet.t) =>
                bind acc (fun (acc : NatSet.t) => if NatSet.mem k acc then None else Some (NatSet.add k acc))
              ) (Some NatSet.empty) l.

  

Definition IG_map_out_keys {A B : Type} (IG_data : NatMap.t (Context' A B)) : option NatSet.t :=
  set_from_list (
    concat (
      map (fun '((_, (_, _, out_map)) : (node * Context' A B)) => map fst (NatMap.elements out_map))
        
      (NatMap.elements IG_data)
    )
  )
.


Definition IG_map_in_keys {A B : Type} (IG_data : NatMap.t (Context' A B)) : option NatSet.t :=
  set_from_list (
    concat (
      map ( fun '((_, (in_map, _, t_step)) : (node * Context' A B)) => map fst (NatMap.elements in_map))
      (NatMap.elements IG_data)
    )
  )
.

Definition IG_nodes_keys {A B : Type} (IG_data : NatMap.t (Context' A B)) : option NatSet.t :=
  set_from_list (map fst (NatMap.elements IG_data))
.


Definition IG_valid_cond_fun {A B : Type} (IG_data : NatMap.t (Context' A B)) : bool :=
  let in_keys := IG_map_in_keys IG_data in
  let out_keys := IG_map_out_keys IG_data in

  let edge_diffs := bind in_keys (fun (in_keys : NatSet.t) => bind out_keys
                                  (fun (out_keys : NatSet.t) => Some (NatSet.diff in_keys out_keys))) in

  let edge_keys := bind in_keys (fun (in_keys : NatSet.t) => bind out_keys
                                  (fun (out_keys : NatSet.t) => Some (NatSet.union in_keys out_keys))) in

  
  let node_keys := IG_nodes_keys IG_data in

  match edge_diffs, edge_keys, node_keys with
  | Some edge_diffs, Some edge_keys, Some node_keys =>
    NatSet.is_empty edge_diffs && NatSet.equal edge_keys node_keys
  | _, _, _ => false
  end
.
  

Definition _valid_cond {A B : Type} (IG_data : NatMap.t (Context' A B)) : Prop :=
  IG_valid_cond_fun IG_data = true.



Definition IG_data_unsafe (A B : Type) : Type :=
  NatMap.t (Context' A B).



(* Advanced theory *)

  gmap f . gmap f 0 = gmap (f . f 0 )
grev . grev = id

We can prove gmap fusion by induction on the graph structure. For g = Empty we
have by definition gmap f (gmap f 0 Empty) = gmap f Empty = Empty = gmap (f . f 0 )
Empty. Otherwise, with g = c & g 0 we conclude by induction:
gmap f (gmap f 0 g) = gmap f (gmap f 0 (c & g 0 ))
= gmap f (f 0 c & (gmap f 0 g 0 ))
= f (f 0 c) & gmap f (gmap f 0 g 0 )
= (f . f 0 ) c & gmap (f . f 0 ) g 0
= gmap (f . f 0 ) (c & g 0 )
= gmap (f . f 0 ) g


swap . swap = id
gmap id = id



grev . grev = gmap swap . gmap swap
= gmap (swap . swap)
= gmap id
= id  *)