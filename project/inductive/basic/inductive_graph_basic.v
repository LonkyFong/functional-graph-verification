Require Import String.
Require Import Coq.Arith.Arith.
Open Scope string_scope.
Require Import Coq.Structures.OrdersTac.

Require Import List.
Require Import Bool.
Import ListNotations.

(* Extreme minimal inductive graph implementation (minimum functions, only integers) with
  {-# MINIMAL empty, isEmpty, match, mkGraph, labNodes #-}
  At the moment, also theorems about them at the bottom of the file.
*)


(* https://rocq-prover.org/doc/v8.9/stdlib/Coq.FSets.FMapList.html *)
Require Import FSets.
Require Import FMaps.
Require Import OrderedTypeEx.

Open Scope nat_scope.

Definition Node := Nat_as_OT.t.


Module NatMap := FMapList.Make(Nat_as_OT).

Module WF := WFacts_fun Nat_as_OT NatMap. (* Library of useful lemmas about maps *)
Module WP := WProperties_fun Nat_as_OT NatMap. (* More useful stuff about maps *)
Print Module WF.
Print Module WP.
Check Nat_as_OT.lt. (*   : positive -> positive -> Prop *)

Module NatSet := FSetList.Make(Nat_as_OT).
Print FSetEqProperties.
Module NatSetProperties := EqProperties(NatSet).



Definition IG : Type :=
  NatMap.t (NatSet.t * NatSet.t).


(* Start defining functionality: *)
Definition empty : IG :=
  NatMap.empty (NatSet.t * NatSet.t).


Definition isEmpty (x : IG) : bool :=
  NatMap.is_empty x.

Compute isEmpty empty.

(* Here start the helper functions for "matsh" *)

(* Applies a function to a map entry if it exists quickly *)
Definition updateEntry (n : Node) (f : (NatSet.t * NatSet.t) -> (NatSet.t * NatSet.t)) (ig : IG) : IG :=
  match NatMap.find n ig with
    | Some v => NatMap.add n (f v) ig
    | None => ig
  end.


Definition cleanUp' (n : Node) (froms tos : NatSet.t) (ig : IG) : IG :=
  (* Loop over ingoing edges of removed node to update the outgoing of all of those to not have n anymore *)
  let ig' := NatSet.fold (fun (elem : Node) (acc : IG) =>
  updateEntry elem (fun '(currFroms, currTos) => (NatSet.remove n currFroms, currTos))
    acc) tos ig in

  (* Loop over outgoing edges of removed node to update the ingoing of all of those to not have n anymore *)
  NatSet.fold (fun (elem : Node) (acc : IG) =>
  updateEntry elem (fun '(currFroms, currTos) => (currFroms, NatSet.remove n currTos))
    acc) froms ig'.
  


Definition cleanUp(n : Node) (context : (NatSet.t * NatSet.t)) (ig : IG) : IG :=
  match context with | (froms, tos) =>
    cleanUp' n froms tos (NatMap.remove n ig)
  end.


Definition matsh (n : Node) (ig : IG) : (option (NatSet.t * NatSet.t) * IG) :=
  match NatMap.find n ig with
    | None => (None, ig)
    | Some context as sContext => (sContext, cleanUp n context ig) 
  end.



(* Here start the helper functions for "mkGraph" *)

(* This is the "&" constructor, but it has to be defined as a function, since it is too advanced *)
Definition add (n : Node) (fromsTos : (NatSet.t * NatSet.t)) (ig : IG) : IG :=
  NatMap.add n fromsTos ig.



Definition insNode (n : Node) (ig : IG) : IG :=
  add n (NatSet.empty, NatSet.empty) ig.
  

Definition insNodes (nodes : list Node) (ig : IG) : IG :=
  fold_right insNode ig nodes.


(* If one of the nodes of the edge does not exist, nothing happens *)
Definition insEdge (edge : (Node * Node)) (ig : IG) : IG :=
match edge with
  | (from, to) =>  if NatMap.mem from ig && NatMap.mem to ig then updateEntry from (fun '(froms, tos) => (froms, NatSet.add to tos))
                (
                  (* Now update the other side of the edge *)
                  updateEntry to (fun '(froms, tos) => (NatSet.add from froms, tos))
                  ig
                ) else ig
end.




Definition insEdges (edges : list (Node * Node)) (ig : IG) : IG :=
  fold_right insEdge ig edges.



Definition mkGraph (nodes : list Node) (edges : list (Node * Node)) : IG :=
  insEdges edges (insNodes nodes empty).


 
Definition labNodes (ig : IG) : list Node :=
  map fst (NatMap.elements ig).



Definition showIG (ig : IG) :=
  map (fun '(node, (froms, tos)) => (node, (NatSet.elements froms, NatSet.elements tos))) (NatMap.elements ig).
  
Definition showDecomp (decomp : (option (NatSet.t * NatSet.t) * IG)) :=
  match decomp with
    | (None, ig) => (None, showIG ig)
    | (Some (froms, tos), ig) => (Some (NatSet.elements froms, NatSet.elements tos), showIG ig)
  end.



Compute showIG (mkGraph [1; 2; 3] [(1, 2); (2, 3); (3, 1)]).

Definition myBasicGraph := mkGraph [1; 2; 3] [(1, 2); (2, 3); (3, 1)].

(* Here come the tests for each defined function (that is in the graph class): *)

Compute showIG empty.

Compute isEmpty empty.
Compute isEmpty myBasicGraph.

Compute showDecomp (matsh 2 myBasicGraph).

Compute showIG (mkGraph [1; 2; 3] [(1, 2); (2, 3); (3, 1)]).

Compute labNodes myBasicGraph.




(* Here, I try out various equational specifications of an IG: *)

(* Block to derive useful conversion theorem "In_labNodes_is_InMap" *)

(* This is from software foundations. Eventually, I will move this somewhere else *)
Lemma eqb_reflect : forall x y, reflect (x = y) (x =? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.eqb_eq.
Qed.
Lemma ltb_reflect : forall x y, reflect (x < y) (x <? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.ltb_lt.
Qed.
Lemma leb_reflect : forall x y, reflect (x <= y) (x <=? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.leb_le.
Qed.

Hint Resolve ltb_reflect leb_reflect eqb_reflect : bdestruct.
Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in
   evar (e: Prop);
   assert (H: reflect e X); subst e;
    [ auto with bdestruct
    | destruct H as [H|H];
       [ | try first [apply not_lt in H | apply not_le in H]]].
(* End from Software foundations *)

Require Import Coq.micromega.Lia.

Check InA.

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

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

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
Lemma In_labNodes_is_InMap : forall (x : Node) (ig : IG),
  In x (labNodes ig) <-> NatMap.In x ig.
Proof.
  intros. unfold labNodes.
  rewrite In_map_fst_InA.
  pose proof (WF.elements_in_iff ig).
  rewrite In_conditions_same in H.
  specialize H with x.
  symmetry.
  assumption.
Qed.


(* Here start "meaningful statements" *)


(* 5 statements on inserting (helpers for mkGraph): update, insEdge, insEdges, insNode, insNodes *)
Lemma updateEntry_does_not_change_key_set : forall (n : Node) (f : NatSet.t * NatSet.t -> NatSet.t * NatSet.t) (ig : IG) (x : Node),
  In x (labNodes (updateEntry n f ig)) <-> In x (labNodes ig).
Proof.
  intros. unfold updateEntry.
  destruct (NatMap.find (elt:=NatSet.t * NatSet.t) n ig) eqn:isIn.
  - rewrite In_labNodes_is_InMap. rewrite In_labNodes_is_InMap. rewrite WF.add_in_iff.
    rewrite WF.in_find_iff. split.
    + intros. destruct H.
      -- rewrite <- H. rewrite isIn. unfold not. intros. discriminate H0.
      -- assumption.
    + intros. right. assumption.
  - reflexivity.
Qed.


Lemma insEdge_does_not_add_node : forall (edge : (Node * Node)) (ig : IG) (x : Node),
  In x (labNodes (insEdge edge ig)) <-> In x (labNodes ig).
Proof.
  intros. unfold insEdge. destruct edge.
  destruct (NatMap.mem (elt:=NatSet.t * NatSet.t) n ig && NatMap.mem (elt:=NatSet.t * NatSet.t) n0 ig) eqn:H0.
  - rewrite updateEntry_does_not_change_key_set.
    rewrite updateEntry_does_not_change_key_set.
    reflexivity.
  - reflexivity.
Qed.


Lemma insEdges_does_not_add_nodes : forall (edges : list (Node * Node)) (ig : IG) (x : Node),
  In x (labNodes (insEdges edges ig)) <-> In x (labNodes ig).
Proof.
  intros. simpl. induction edges.
  - simpl. reflexivity.
  - simpl. rewrite insEdge_does_not_add_node. rewrite IHedges. reflexivity.
Qed. 


Lemma insNode_any_ins_node : forall (node : Node) (ig : IG) (x : Node),
  In x (labNodes (insNode node ig)) <-> In x (node :: labNodes ig).
Proof.
  intros. simpl. unfold insNode.
  rewrite In_labNodes_is_InMap. rewrite WF.add_in_iff.
  rewrite In_labNodes_is_InMap.
  reflexivity.
Qed.  


Lemma insNodes_any_ins_all_nodes : forall (nodes : list Node) (ig : IG) (x : Node),
  In x (labNodes (insNodes nodes ig)) <-> In x (nodes ++ labNodes ig).
Proof.
  intros. induction nodes.
    - simpl. reflexivity.
    - simpl. rewrite insNode_any_ins_node. simpl. rewrite IHnodes. reflexivity.
Qed.

Lemma insEdge_on_empty_is_empty : forall (edge : Node * Node),
  insEdge edge empty = empty.
(* This proof is very similar to "insEdge_does_not_add_node", but using it here it is more complicated than just doing it again  *)
Proof.
  intros. unfold insEdge. destruct edge.
  destruct (NatMap.mem (elt:=NatSet.t * NatSet.t) n empty && NatMap.mem (elt:=NatSet.t * NatSet.t) n0 empty) eqn:cond.
  - compute. reflexivity.
  - reflexivity.
Qed. 


Lemma insEdges_on_empty_is_empty : forall (edges : list (Node * Node)),
  insEdges edges empty = empty.
(* This proof is very similar to "insEdges_does_not_add_nodes", but using it here it is more complicated than just doing it again  *)
Proof.
  intros. induction edges; simpl.
  - reflexivity.
  - rewrite IHedges. rewrite insEdge_on_empty_is_empty. reflexivity.
Qed.



(* "big" statement: *)
Theorem mkGraph_any_ins_all_nodes : forall (nl : list Node) (el : list (Node * Node)) (x : Node),
  In x (labNodes (mkGraph nl el)) <-> In x nl.
Proof.
  intros. unfold mkGraph. rewrite insEdges_does_not_add_nodes. rewrite insNodes_any_ins_all_nodes.
  rewrite app_nil_r. reflexivity.
Qed.


Theorem empty_isEmpty : isEmpty empty = true.
Proof.
  compute. reflexivity.
Qed.

Theorem labNodes_empty_nil : labNodes empty = [].
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
  length nodes <> 0 <-> isEmpty ((mkGraph nodes edges)) = false.
Proof.
  intros. unfold isEmpty. rewrite <- not_NatMap_Empty_is_empty_false. unfold not.
  destruct nodes; simpl; unfold mkGraph.
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



Theorem matsh_empty_is_nothing : forall (node : Node), matsh node empty = (None, empty).
Proof.
  intros. compute. reflexivity.
Qed.


Theorem spec4 : forall (node : Node) (nodes : list Node) (edges : list (Node * Node)), 
  In node nodes -> exists froms tos, matsh node (mkGraph nodes edges) =
  (Some (froms, tos), mkGraph (filter (fun n => negb (node =? n)) nodes) (filter (fun '(from, to) => negb ((from =? node) || (to =? node))) edges)).
(* This is not even a complete specification and it looks like a hard one to prove... *)
Proof.
Admitted.


Theorem spec5 : forall (node : Node) (nodes : list Node) (edges : list (Node * Node)), 
  not (In node nodes) -> matsh node (mkGraph nodes edges) = (None, mkGraph nodes edges).
Proof.
Admitted.