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
Definition updateEntry (node : Node) (f : (NatSet.t * NatSet.t) -> (NatSet.t * NatSet.t)) (ig : IG) : IG :=
  match NatMap.find node ig with
    | Some v => NatMap.add node (f v) ig
    | None => ig
  end.


Definition cleanUp' (node : Node) (froms tos : NatSet.t) (ig : IG) : IG :=
  (* Loop over ingoing edges of removed node to update the outgoing of all of those to not have n anymore *)
  let ig' := NatSet.fold (fun (elem : Node) (acc : IG) =>
  updateEntry elem (fun '(currFroms, currTos) => (NatSet.remove node currFroms, currTos))
    acc) tos ig in

  (* Loop over outgoing edges of removed node to update the ingoing of all of those to not have n anymore *)
  NatSet.fold (fun (elem : Node) (acc : IG) =>
  updateEntry elem (fun '(currFroms, currTos) => (currFroms, NatSet.remove node currTos))
    acc) froms ig'.
  


Definition cleanUp (node : Node) (context : (NatSet.t * NatSet.t)) (ig : IG) : IG :=
  match context with | (froms, tos) =>
    cleanUp' node froms tos (NatMap.remove node ig)
  end.


Definition matsh (node : Node) (ig : IG) : (option (NatSet.t * NatSet.t) * IG) :=
  match NatMap.find node ig with
    | None => (None, ig)
    | Some context as sContext => (sContext, cleanUp node context ig) 
  end.



(* Here start the helper functions for "mkGraph" *)

(* This is the "&" constructor, but it has to be defined as a function, since it is too advanced *)
Definition add (node : Node) (fromsTos : (NatSet.t * NatSet.t)) (ig : IG) : IG :=
  NatMap.add node fromsTos ig.



Definition insNode (node : Node) (ig : IG) : IG :=
  add node (NatSet.empty, NatSet.empty) ig.
  

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



(* Make IG_basic visible *)

Definition showIG (ig : IG) :=
  map (fun '(node, (froms, tos)) => (node, (NatSet.elements froms, NatSet.elements tos))) (NatMap.elements ig).
  
Definition showDecomp (decomp : (option (NatSet.t * NatSet.t) * IG)) :=
  match decomp with
    | (None, ig) => (None, showIG ig)
    | (Some (froms, tos), ig) => (Some (NatSet.elements froms, NatSet.elements tos), showIG ig)
  end.





(* TODO: this should relocate to "examples" after big rename *)
Compute showIG (mkGraph [1; 2; 3] [(1, 2); (2, 3); (3, 1)]).

Definition myBasicGraph := mkGraph [1; 2; 3] [(1, 2); (2, 3); (3, 1)].

(* Here come the tests for each defined function (that is in the graph class): *)

Compute showIG empty.

Compute isEmpty empty.
Compute isEmpty myBasicGraph.

Compute showDecomp (matsh 2 myBasicGraph).

Compute showIG (mkGraph [1; 2; 3] [(1, 2); (2, 3); (3, 1)]).

Compute labNodes myBasicGraph.

