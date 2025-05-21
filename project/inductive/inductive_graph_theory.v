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





Lemma _insEdge_does_not_add_node : forall (A B : Type) (edge : LEdge B) (ig : IG A B) (x : LNode A),
  In x (IG_labNodes (_insEdge edge ig)) <-> In x (IG_labNodes ig).
Proof.
Admitted.
  (* intros. unfold _insEdge. destruct edge.
  destruct (NatMap.mem (elt:=NatSet.t * NatSet.t) n ig && NatMap.mem (elt:=NatSet.t * NatSet.t) n0 ig) eqn:H0.
  - rewrite _updateEntry_does_not_change_key_set.
    rewrite _updateEntry_does_not_change_key_set.
    reflexivity.
  - reflexivity.
Qed. *)


Lemma _insEdges_does_not_add_nodes : forall (A B : Type) (edges : list (LEdge B)) (ig : IG A B) (x : LNode A), 
  In x (IG_labNodes (_insEdges edges ig)) <-> In x (IG_labNodes ig).
Proof.
  intros. simpl. induction edges.
  - simpl. reflexivity.
  - simpl. rewrite _insEdge_does_not_add_node. rewrite IHedges. reflexivity.
Qed. 


Lemma _insNode_any_ins_node : forall (A B : Type) (node : LNode A) (ig : IG A B) (x : LNode A),
  In x (IG_labNodes (_insNode node ig)) <-> In x (node :: IG_labNodes ig).
Proof.
Admitted.
  (* intros. simpl. unfold _insNode.
  rewrite _In_labNodes_is_InMap. rewrite WF.add_mapsto_iff.
  rewrite _In_labNodes_is_InMap.
  reflexivity.
Qed. *)


Lemma _insNodes_any_ins_all_nodes : forall (A B : Type) (nodes : list (LNode A)) (ig : IG A B) (x : LNode A),
  In x (IG_labNodes (_insNodes nodes ig)) <-> In x (nodes ++ IG_labNodes ig).
Proof.
  intros. induction nodes.
    - simpl. reflexivity.
    - simpl. rewrite _insNode_any_ins_node. simpl. rewrite IHnodes. reflexivity.
Qed.

Lemma _insEdge_on_empty_is_empty : forall (A B : Type) (edge : LEdge B),
  _insEdge edge (@IG_empty A B)= IG_empty. 
(* This proof is very similar to "insEdge_does_not_add_node", but using it here it is more complicated than just doing it again  *)
Proof.
Admitted.
  (* intros. unfold _insEdge. destruct edge.
  destruct (NatMap.mem (elt:=NatSet.t * NatSet.t) n IG_empty && NatMap.mem (elt:=NatSet.t * NatSet.t) n0 IG_empty) eqn:cond.
  - compute. reflexivity.
  - reflexivity.
Qed.  *)


Lemma _insEdges_on_empty_is_empty : forall (A B : Type) (edges : list (LEdge B)),
  _insEdges edges (@IG_empty A B) = IG_empty.
(* This proof is very similar to "insEdges_does_not_add_nodes", but using it here it is more complicated than just doing it again  *)
Proof.
  intros. induction edges; simpl.
  - reflexivity.
  - rewrite IHedges. rewrite _insEdge_on_empty_is_empty. reflexivity.
Qed.



(* "big" statement: *)
Theorem IG_mkGraph_any_ins_all_nodes : forall (A B : Type) (nl : list (LNode A)) (el : list (LEdge B)) (x : LNode A),
  In x (IG_labNodes (IG_mkGraph nl el)) <-> In x nl.
Proof.
  intros. unfold IG_mkGraph. rewrite _insEdges_does_not_add_nodes. rewrite _insNodes_any_ins_all_nodes.
  rewrite app_nil_r. reflexivity.
Qed.


Theorem IG_empty_isEmpty : forall (A B : Type), IG_isEmpty (@IG_empty A B) = true.
Proof.
  compute. reflexivity.
Qed.

Theorem IG_labNodes_empty_nil : forall (A B : Type), IG_labNodes (@IG_empty A B) = [].
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
Theorem  IG_non_empty_isEmpty_false : forall (A B : Type) (nodes : list (LNode A)) (edges : list (LEdge B)),
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



Theorem IG_matsh_empty_is_nothing : forall (A B : Type) (node : Node), IG_match node (@IG_empty A B) = (None, IG_empty).   
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