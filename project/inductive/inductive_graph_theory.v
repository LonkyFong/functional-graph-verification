(* Require Import Coq.micromega.Lia.
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

(* This file shows that I== is an equivalence and attempts at "direct equational specification" of IG s  *)


(* Section to make rewrite work with IG_equiv *)
(* This proof is based on === being an equivalence relation *)
Instance IG_Equivalence {A B : Type} : Equivalence (@IG_equiv A B).
Proof.
  G_derived_equivalence_prover nat unit (@ IG_to_RG A B).  
Qed.


(* (attempt at) direct equational specifications of an IG: *)

(* Block to derive useful conversion theorem "In_labNodes_is_InMap" *)


(* Helper lemma for converting an In (of a map) to an InA, which will eventually be turned to a NatMap.In (which has useful lemmas)  *)
Lemma _In_map_fst_InA : forall (A B: Type) (a : A) (l : list (A * B)),
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
Lemma _In_conditions_same : (NatMap.eq_key_elt (elt:=NatSet.t * NatSet.t)) = (fun x el : Node * (NatSet.t * NatSet.t) => x = el).
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
Lemma _In_labNodes_is_InMap : forall (x : Node) (ig : IG),
  In x (IG_labNodes ig) <-> NatMap.In x ig.
Proof.
  intros. unfold IG_labNodes.
  rewrite _In_map_fst_InA.
  pose proof (WF.elements_in_iff ig).
  rewrite _In_conditions_same in H.
  specialize H with x.
  symmetry.
  assumption.
Qed.


(* Here start "meaningful statements" *)


(* 5 statements on inserting (helpers for mkGraph): update, insEdge, insEdges, insNode, insNodes *)
Lemma _updateEntry_does_not_change_key_set : forall (node : Node) (f : NatSet.t * NatSet.t -> NatSet.t * NatSet.t) (ig : IG) (x : Node),
  In x (IG_labNodes (_updateEntry node f ig)) <-> In x (IG_labNodes ig).
Proof.
  intros. unfold _updateEntry.
  destruct (NatMap.find (elt:=NatSet.t * NatSet.t) node ig) eqn:isIn.
  - rewrite _In_labNodes_is_InMap. rewrite _In_labNodes_is_InMap. rewrite WF.add_in_iff.
    rewrite WF.in_find_iff. split.
    + intros. destruct H.
      -- rewrite <- H. rewrite isIn. unfold not. intros. discriminate H0.
      -- assumption.
    + intros. right. assumption.
  - reflexivity.
Qed.


Lemma _insEdge_does_not_add_node : forall (edge : (Node * Node)) (ig : IG) (x : Node),
  In x (IG_labNodes (_insEdge edge ig)) <-> In x (IG_labNodes ig).
Proof.
  intros. unfold _insEdge. destruct edge.
  destruct (NatMap.mem (elt:=NatSet.t * NatSet.t) n ig && NatMap.mem (elt:=NatSet.t * NatSet.t) n0 ig) eqn:H0.
  - rewrite _updateEntry_does_not_change_key_set.
    rewrite _updateEntry_does_not_change_key_set.
    reflexivity.
  - reflexivity.
Qed.


Lemma _insEdges_does_not_add_nodes : forall (edges : list (Node * Node)) (ig : IG) (x : Node),
  In x (IG_labNodes (_insEdges edges ig)) <-> In x (IG_labNodes ig).
Proof.
  intros. simpl. induction edges.
  - simpl. reflexivity.
  - simpl. rewrite _insEdge_does_not_add_node. rewrite IHedges. reflexivity.
Qed. 


Lemma _insNode_any_ins_node : forall (node : Node) (ig : IG) (x : Node),
  In x (IG_labNodes (_insNode node ig)) <-> In x (node :: IG_labNodes ig).
Proof.
  intros. simpl. unfold _insNode.
  rewrite _In_labNodes_is_InMap. rewrite WF.add_in_iff.
  rewrite _In_labNodes_is_InMap.
  reflexivity.
Qed.  


Lemma _insNodes_any_ins_all_nodes : forall (nodes : list Node) (ig : IG) (x : Node),
  In x (IG_labNodes (_insNodes nodes ig)) <-> In x (nodes ++ IG_labNodes ig).
Proof.
  intros. induction nodes.
    - simpl. reflexivity.
    - simpl. rewrite _insNode_any_ins_node. simpl. rewrite IHnodes. reflexivity.
Qed.

Lemma _insEdge_on_empty_is_empty : forall (edge : Node * Node),
  _insEdge edge IG_empty = IG_empty.
(* This proof is very similar to "insEdge_does_not_add_node", but using it here it is more complicated than just doing it again  *)
Proof.
  intros. unfold _insEdge. destruct edge.
  destruct (NatMap.mem (elt:=NatSet.t * NatSet.t) n IG_empty && NatMap.mem (elt:=NatSet.t * NatSet.t) n0 IG_empty) eqn:cond.
  - compute. reflexivity.
  - reflexivity.
Qed. 


Lemma _insEdges_on_empty_is_empty : forall (edges : list (Node * Node)),
  _insEdges edges IG_empty = IG_empty.
(* This proof is very similar to "insEdges_does_not_add_nodes", but using it here it is more complicated than just doing it again  *)
Proof.
  intros. induction edges; simpl.
  - reflexivity.
  - rewrite IHedges. rewrite _insEdge_on_empty_is_empty. reflexivity.
Qed.



(* "big" statement: *)
Theorem IG_mkGraph_any_ins_all_nodes : forall (nl : list Node) (el : list (Node * Node)) (x : Node),
  In x (IG_labNodes (IG_mkGraph nl el)) <-> In x nl.
Proof.
  intros. unfold IG_mkGraph. rewrite _insEdges_does_not_add_nodes. rewrite _insNodes_any_ins_all_nodes.
  rewrite app_nil_r. reflexivity.
Qed.


Theorem IG_empty_isEmpty : IG_isEmpty IG_empty = true.
Proof.
  compute. reflexivity.
Qed.

Theorem IG_labNodes_empty_nil : IG_labNodes IG_empty = [].
Proof.
  compute. reflexivity.
Qed.


Lemma _not_NatMap_Empty_is_empty_false : forall (A : Type) (m : NatMap.t A), not (NatMap.Empty m) <-> NatMap.is_empty m = false.
Proof.
  intros. unfold not. rewrite WF.is_empty_iff. destruct (NatMap.is_empty (elt:=A) m) eqn:cond.
  - firstorder. congruence.
  - firstorder. congruence.
Qed.

(* Think about enforcing non-emptiness of the list with (x::xs) *)
Theorem  IG_non_empty_isEmpty_false : forall (nodes : list Node) (edges : list (Node * Node)),
  length nodes <> 0 <-> IG_isEmpty ((IG_mkGraph nodes edges)) = false.
Proof.
  intros. unfold IG_isEmpty. rewrite <- _not_NatMap_Empty_is_empty_false. unfold not.
  destruct nodes; simpl; unfold IG_mkGraph.
  - firstorder.
    apply H.
    apply WP.elements_Empty.

    rewrite _insEdges_on_empty_is_empty. compute. reflexivity.
  - firstorder.
    + apply WP.elements_Empty in H0.
      assert (HH : not (exists e, InA (fun x el : Node * (NatSet.t * NatSet.t) => x = el) (n, e) [])). {
        unfold not. intros. destruct H1. inversion H1.
      }
      rewrite <- _In_conditions_same in HH.

      unfold not in HH. apply HH.
      
      pose proof WF.elements_in_iff.
      edestruct H1.
      rewrite H0 in H2.
      apply H2.
      
      apply _In_labNodes_is_InMap.
      apply IG_mkGraph_any_ins_all_nodes. simpl. left. reflexivity.
    + congruence.
Qed.



Theorem IG_matsh_empty_is_nothing : forall (node : Node), IG_match node IG_empty = (None, IG_empty).
Proof.
  intros. compute. reflexivity.
Qed.


Theorem IG_spec4 : forall (node : Node) (nodes : list Node) (edges : list (Node * Node)), 
  In node nodes -> exists froms tos, IG_match node (IG_mkGraph nodes edges) =
  (Some (froms, tos), IG_mkGraph (filter (fun n => negb (node =? n)) nodes) (filter (fun '(from, to) => negb ((from =? node) || (to =? node))) edges)).
(* This is not even a complete specification and it looks like a hard one to prove... *)
Proof.
  intros.
  
Admitted.


Theorem IG_spec5 : forall (node : Node) (nodes : list Node) (edges : list (Node * Node)), 
  not (In node nodes) -> IG_match node (IG_mkGraph nodes edges) = (None, IG_mkGraph nodes edges).
Proof.
Admitted.






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
= id *)