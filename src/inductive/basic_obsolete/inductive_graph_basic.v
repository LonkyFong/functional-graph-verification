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


Require Import FMaps.
Require Import OrderedTypeEx.

Open Scope nat_scope.


Module NatMap := FMapList.Make(Nat_as_OT).

Module WF := WFacts_fun Nat_as_OT NatMap. (* Library of useful lemmas about maps *)
Module WP := WProperties_fun Nat_as_OT NatMap. (* More useful stuff about maps *)
Print Module MFacts.
Print Module MProps.
Check Nat_as_OT.lt. (*   : positive -> positive -> Prop *)


Require Import GraphVerification.src.util.NatSet.

Print FSetEqProperties.



Definition IG_basic : Type :=
  NatMap.t (NatSet.t * NatSet.t).


(* Start defining functionality: *)
Definition IG_basic_empty : IG_basic :=
  NatMap.empty (NatSet.t * NatSet.t).


Definition IG_basic_isEmpty (x : IG_basic) : bool :=
  NatMap.is_empty x.

Compute IG_basic_isEmpty IG_basic_empty.

(* Here start the helper functions for "match" *)

(* Applies a function to a map entry if it exists quickly *)
Definition _updateEntry (node : Node) (f : (NatSet.t * NatSet.t) -> (NatSet.t * NatSet.t)) (ig : IG_basic) : IG_basic :=
  match NatMap.find node ig with
    | Some v => NatMap.add node (f v) ig
    | None => ig
  end.


Definition _cleanUp' (node : Node) (froms tos : NatSet.t) (ig : IG_basic) : IG_basic :=
  (* Loop over ingoing edges of removed node to update the outgoing of all of those to not have n anymore *)
  let ig' := NatSet.fold (fun (elem : Node) (acc : IG_basic) =>
  _updateEntry elem (fun '(currFroms, currTos) => (NatSet.remove node currFroms, currTos))
    acc) tos ig in

  (* Loop over outgoing edges of removed node to update the ingoing of all of those to not have n anymore *)
  NatSet.fold (fun (elem : Node) (acc : IG_basic) =>
  _updateEntry elem (fun '(currFroms, currTos) => (currFroms, NatSet.remove node currTos))
    acc) froms ig'.
  


Definition _cleanUp (node : Node) (context : (NatSet.t * NatSet.t)) (ig : IG_basic) : IG_basic :=
  match context with | (froms, tos) =>
    _cleanUp' node froms tos (NatMap.remove node ig)
  end.


Definition IG_basic_match (node : Node) (ig : IG_basic) : (option (NatSet.t * NatSet.t) * IG_basic) :=
  match NatMap.find node ig with
    | None => (None, ig)
    | Some context as sContext => (sContext, _cleanUp node context ig) 
  end.



(* Here start the helper functions for "mkGraph" *)

(* This is the "&" constructor, but it has to be defined as a function, since it is too advanced *)
(* So far does not guarantee safety *)
Definition _add (node : Node) (fromsTos : (NatSet.t * NatSet.t)) (ig : IG_basic) : IG_basic :=
  NatMap.add node fromsTos ig.



Definition _insNode (node : Node) (ig : IG_basic) : IG_basic :=
  _add node (NatSet.empty, NatSet.empty) ig.
  

Definition _insNodes (nodes : list Node) (ig : IG_basic) : IG_basic :=
  fold_right _insNode ig nodes.


(* If one of the nodes of the edge does not exist, nothing happens *)
Definition _insEdge (edge : (Node * Node)) (ig : IG_basic) : IG_basic :=
match edge with
  | (from, to) =>  if NatMap.mem from ig && NatMap.mem to ig then _updateEntry from (fun '(froms, tos) => (froms, NatSet.add to tos))
                (
                  (* Now update the other side of the edge *)
                  _updateEntry to (fun '(froms, tos) => (NatSet.add from froms, tos))
                  ig
                ) else ig
end.




Definition _insEdges (edges : list (Node * Node)) (ig : IG_basic) : IG_basic :=
  fold_right _insEdge ig edges.



Definition IG_basic_mkGraph (nodes : list Node) (edges : list (Node * Node)) : IG_basic :=
  _insEdges edges (_insNodes nodes IG_basic_empty).


 
Definition IG_basic_labNodes (ig : IG_basic) : list Node :=
  map fst (NatMap.elements ig).



(* Make IG_basic visible *)

Definition IG_basic_showIG (ig : IG_basic) :=
  map (fun '(node, (froms, tos)) => (node, (NatSet.elements froms, NatSet.elements tos))) (NatMap.elements ig).
  
Definition IG_basic_showDecomp (decomp : (option (NatSet.t * NatSet.t) * IG_basic)) :=
  match decomp with
    | (None, ig) => (None, IG_basic_showIG ig)
    | (Some (froms, tos), ig) => (Some (NatSet.elements froms, NatSet.elements tos), IG_basic_showIG ig)
  end.




