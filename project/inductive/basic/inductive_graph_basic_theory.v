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

Require Import MyProject.project.inductive.basic.inductive_graph_basic.
Require Import MyProject.project.inductive.basic.inductive_graph_basic_to_RG.

Require Import MyProject.project.relational_graph.
Require Import MyProject.project.relational_graph_theory.

(* This file shows that I== is an equivalence and attempts at "direct equational specification" of IG_basic s  *)


(* Section to make rewrite work with IG_equiv *)
(* This proof is based on === being an equivalence relation *)
Instance IG_Equivalence_eq : Equivalence IG_basic_equiv.
Proof.
  G_derived_equivalence_prover nat IG_basic_to_RG.
Qed.


(* (attempt at) direct equational specifications of an IG_basic: *)


(* Block to derive useful conversion theorem "In_labNodes_is_InMap" *)


(* Helper lemma for converting an In (of a map) to an InA, which will eventually be turned to a NatMap.In (which has useful lemmas)  *)
Lemma In_map_fst_InA : forall (A B: Type) (a : A) (l : list (A * B)),
  In a (map fst l) <-> exists (a0 : B), InA (fun (x el : (A * B)) => x = el) (a, a0) l.
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
      -- left. destruct a0. destruct H1. simpl. reflexivity.
      -- right. apply IHl. exists x. assumption.
Qed.  



(* Conversion from key equality from map to my own (simply written in a slightly different manner) *)
Lemma In_conditions_same : (NatMap.eq_key_elt (elt:=NatSet.t * NatSet.t)) = (fun x el : Node * (NatSet.t * NatSet.t) => x = el).
Proof.
  unfold NatMap.eq_key_elt. unfold NatMap.Raw.PX.eqke.
  apply functional_extensionality.
  intros.
  apply functional_extensionality.
  intros.
  destruct x, x0.
  simpl.
  apply propositional_extensionality.
  split; intros.
  - destruct H. subst. reflexivity.
  - inversion H. auto.
Qed.

(* This is the most useful one for proving other statements.
  Use it to convert from "use friendly" In- statements to "provable" NatMap.In- statements  *)
Lemma In_labNodes_is_InMap : forall (x : Node) (ig : IG_basic),
  In x (IG_basic_labNodes ig) <-> NatMap.In x ig.
Proof.
  intros. unfold IG_basic_labNodes.
  rewrite In_map_fst_InA.
  pose proof (WF.elements_in_iff ig).
  rewrite In_conditions_same in H.
  specialize H with x.
  symmetry.
  assumption.
Qed.


(* Here start "meaningful statements" *)


(* 5 statements on inserting (helpers for mkGraph): update, insEdge, insEdges, insNode, insNodes *)
Lemma updateEntry_does_not_change_key_set : forall (node : Node) (f : NatSet.t * NatSet.t -> NatSet.t * NatSet.t) (ig : IG_basic) (x : Node),
  In x (IG_basic_labNodes (_updateEntry node f ig)) <-> In x (IG_basic_labNodes ig).
Proof.
  intros. unfold _updateEntry.
  destruct (NatMap.find (elt:=NatSet.t * NatSet.t) node ig) eqn:isIn.
  - rewrite In_labNodes_is_InMap. rewrite In_labNodes_is_InMap. rewrite WF.add_in_iff.
    rewrite WF.in_find_iff. split.
    + intros. destruct H.
      -- rewrite <- H. rewrite isIn. unfold not. intros. discriminate H0.
      -- assumption.
    + intros. right. assumption.
  - reflexivity.
Qed.


Lemma insEdge_does_not_add_node : forall (edge : (Node * Node)) (ig : IG_basic) (x : Node),
  In x (IG_basic_labNodes (_insEdge edge ig)) <-> In x (IG_basic_labNodes ig).
Proof.
  intros. unfold _insEdge. destruct edge.
  destruct (NatMap.mem (elt:=NatSet.t * NatSet.t) n ig && NatMap.mem (elt:=NatSet.t * NatSet.t) n0 ig) eqn:H0.
  - rewrite updateEntry_does_not_change_key_set.
    rewrite updateEntry_does_not_change_key_set.
    reflexivity.
  - reflexivity.
Qed.


Lemma insEdges_does_not_add_nodes : forall (edges : list (Node * Node)) (ig : IG_basic) (x : Node),
  In x (IG_basic_labNodes (_insEdges edges ig)) <-> In x (IG_basic_labNodes ig).
Proof.
  intros. simpl. induction edges.
  - simpl. reflexivity.
  - simpl. rewrite insEdge_does_not_add_node. rewrite IHedges. reflexivity.
Qed. 


Lemma insNode_any_ins_node : forall (node : Node) (ig : IG_basic) (x : Node),
  In x (IG_basic_labNodes (_insNode node ig)) <-> In x (node :: IG_basic_labNodes ig).
Proof.
  intros. simpl. unfold _insNode.
  rewrite In_labNodes_is_InMap. rewrite WF.add_in_iff.
  rewrite In_labNodes_is_InMap.
  reflexivity.
Qed.  


Lemma insNodes_any_ins_all_nodes : forall (nodes : list Node) (ig : IG_basic) (x : Node),
  In x (IG_basic_labNodes (_insNodes nodes ig)) <-> In x (nodes ++ IG_basic_labNodes ig).
Proof.
  intros. induction nodes.
    - simpl. reflexivity.
    - simpl. rewrite insNode_any_ins_node. simpl. rewrite IHnodes. reflexivity.
Qed.

Lemma insEdge_on_empty_is_empty : forall (edge : Node * Node),
  _insEdge edge IG_basic_empty = IG_basic_empty.
(* This proof is very similar to "insEdge_does_not_add_node", but using it here it is more complicated than just doing it again  *)
Proof.
  intros. unfold _insEdge. destruct edge.
  destruct (NatMap.mem (elt:=NatSet.t * NatSet.t) n IG_basic_empty && NatMap.mem (elt:=NatSet.t * NatSet.t) n0 IG_basic_empty) eqn:cond.
  - compute. reflexivity.
  - reflexivity.
Qed. 


Lemma insEdges_on_empty_is_empty : forall (edges : list (Node * Node)),
  _insEdges edges IG_basic_empty = IG_basic_empty.
(* This proof is very similar to "insEdges_does_not_add_nodes", but using it here it is more complicated than just doing it again  *)
Proof.
  intros. induction edges; simpl.
  - reflexivity.
  - rewrite IHedges. rewrite insEdge_on_empty_is_empty. reflexivity.
Qed.



(* "big" statement: *)
Theorem mkGraph_any_ins_all_nodes : forall (nl : list Node) (el : list (Node * Node)) (x : Node),
  In x (IG_basic_labNodes (IG_basic_mkGraph nl el)) <-> In x nl.
Proof.
  intros. unfold IG_basic_mkGraph. rewrite insEdges_does_not_add_nodes. rewrite insNodes_any_ins_all_nodes.
  rewrite app_nil_r. reflexivity.
Qed.


Theorem empty_isEmpty : IG_basic_isEmpty IG_basic_empty = true.
Proof.
  compute. reflexivity.
Qed.

Theorem labNodes_empty_nil : IG_basic_labNodes IG_basic_empty = [].
Proof.
  compute. reflexivity.
Qed.


(* Protipp: firstorder and congruence seem pretty useful *)
Lemma not_NatMap_Empty_is_empty_false : forall (A : Type) (m : NatMap.t A), not (NatMap.Empty m) <-> NatMap.is_empty m = false.
Proof.
  intros. unfold not. rewrite WF.is_empty_iff. destruct (NatMap.is_empty (elt:=A) m) eqn:cond.
  - firstorder. congruence.
  - firstorder. congruence.
Qed.


Theorem  non_empty_isEmpty_false : forall (nodes : list Node) (edges : list (Node * Node)),
  length nodes <> 0 <-> IG_basic_isEmpty ((IG_basic_mkGraph nodes edges)) = false.
Proof.
  intros. unfold IG_basic_isEmpty. rewrite <- not_NatMap_Empty_is_empty_false. unfold not.
  destruct nodes; simpl; unfold IG_basic_mkGraph.
  - firstorder.
    apply H.
    apply WP.elements_Empty.

    rewrite insEdges_on_empty_is_empty. compute. reflexivity.
  - firstorder.
    + apply WP.elements_Empty in H0.
      assert (HH : not (exists e, InA (fun x el : Node * (NatSet.t * NatSet.t) => x = el) (n, e) [])). {
        unfold not. intros. destruct H1. inversion H1.
      }
      rewrite <- In_conditions_same in HH.

      unfold not in HH. apply HH.
      
      pose proof WF.elements_in_iff.
      edestruct H1.
      rewrite H0 in H2.
      apply H2.
      
      apply In_labNodes_is_InMap.
      apply mkGraph_any_ins_all_nodes. simpl. left. reflexivity.
    + congruence.
Qed.



Theorem matsh_empty_is_nothing : forall (node : Node), IG_basic_match node IG_basic_empty = (None, IG_basic_empty).
Proof.
  intros. compute. reflexivity.
Qed.


Theorem spec4 : forall (node : Node) (nodes : list Node) (edges : list (Node * Node)), 
  In node nodes -> exists froms tos, IG_basic_match node (IG_basic_mkGraph nodes edges) =
  (Some (froms, tos), IG_basic_mkGraph (filter (fun n => negb (node =? n)) nodes) (filter (fun '(from, to) => negb ((from =? node) || (to =? node))) edges)).
(* This is not even a complete specification and it looks like a hard one to prove... *)
Proof.
Admitted.


Theorem spec5 : forall (node : Node) (nodes : list Node) (edges : list (Node * Node)), 
  not (In node nodes) -> IG_basic_match node (IG_basic_mkGraph nodes edges) = (None, IG_basic_mkGraph nodes edges).
Proof.
Admitted.