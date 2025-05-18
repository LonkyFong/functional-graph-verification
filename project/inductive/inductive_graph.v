Require Import Coq.Arith.Arith.
Require Import String.
Open Scope string_scope.

Require Import Bool.
Require Import List.
Import ListNotations.

Require Import MyProject.project.util.NatMap.
Require Import MyProject.project.util.NatSet.
Open Scope nat_scope.

(* This file defines an inductive graph using maps like Erwig *)
(* Note that A is the node label type and B is the edge label type *)
(* At the moment, there are only the "MINIMAL" implementations  *)

(*{-# MINIMAL empty, isEmpty, match, mkGraph, labNodes #-}
  *)

Definition Adj (B : Type) := list (B * Node). 

Definition Context (A B : Type) : Type :=
    (Adj B * Node * A * Adj B).

Definition MContext (A B : Type) : Type :=
    option (Context A B).


(* Definition Adj' (B : Type) := NatMap.t (list B). *)

(* No node needed, since the node is the key *)
Definition Context' (A B : Type) : Type :=
  (Adj B * A * Adj B).  

Definition IG (A B : Type) := NatMap.t (Context' A B).

Definition Decomp (A B : Type) : Type :=
  (MContext A B * IG A B). 


Definition LNode (A : Type) : Type := (Node * A).
Definition LEdge (B : Type) : Type := (Node * Node * B).





(* Start defining functionality: *)
Definition IG_empty {A B : Type} : IG A B :=
  NatMap.empty (Context' A B).


Definition IG_isEmpty {A B : Type} (ig : IG A B) : bool :=
  NatMap.is_empty ig.

Compute IG_isEmpty IG_empty.



(* Here start the helper functions for "match" *)




(* Applies a function to a map entry if it exists quickly *)
Definition _updateEntry {A B : Type} (node : Node) (f : Context' A B -> Context' A B) (ig : IG A B) : IG A B := 
  match NatMap.find node ig with
    | Some v => NatMap.add node (f v) ig
    | None => ig
  end.

Definition _addSucc {A B : Type} (node : Node) (label : B) (context' : Context' A B) : Context' A B :=
  match context' with
  | (froms, l, tos) => (froms, l, (label, node) :: tos)
  end.
  
Definition _addPred {A B : Type} (node : Node) (label : B) (context' : Context' A B) : Context' A B :=
  match context' with
  | (froms, l, tos) => ((label, node) :: froms, l, tos)
  end.


Definition _clearSucc {A B : Type} (node : Node) (context' : Context' A B) : Context' A B :=
  match context' with
  | (froms, label, tos) => (froms, label, filter (fun '(_, n) => negb (n =? node)) tos)
  end.


Definition _clearPred {A B : Type} (node : Node) (context' : Context' A B) : Context' A B :=
  match context' with
  | (froms, label, tos) => (filter (fun '(_, n) => negb (n =? node)) froms, label, tos)
  end.


Definition _updAdj {A B : Type} (adj : Adj B) (f : B -> Context' A B -> Context' A B) (gr : IG A B) : IG A B :=
  fold_right (fun '(l, n) (acc : IG A B) => _updateEntry n (f l) acc) gr adj.  


Definition _cleanSplit {A B : Type} (node : Node) (context' : Context' A B) (ig : IG A B) : Context A B * IG A B :=
  match context' with
  | (froms, label, tos) =>
                          let rmLoops :=  filter (fun '(_, n) => negb (n =? node)) in
                          let froms' := rmLoops froms in
                          let tos' := rmLoops tos in
                          let context := (froms', node, label, tos (*no '*)) in
                          
                          let ig' := _updAdj froms' (fun x y => _clearPred node y) ig in
                          let ig'' := _updAdj tos' (fun x y => _clearSucc node y) ig' in
                          (context, ig'')
  end.


Definition IG_match {A B : Type} (node : Node) (ig : IG A B) : Decomp A B :=
  match NatMap.find node ig with
  | None => (None, ig)
  | Some context' => match _cleanSplit node context' (NatMap.remove node ig) with
                    | (context, ig') => (Some context, ig')
                    end
  end.




(* Here start the helper functions for "mkGraph" *)

(* This is the "&" constructor, but it has to be defined as a function, since it is too advanced *)
Definition add {A B : Type} (context : Context A B) (ig : IG A B) : IG A B :=
  match context with
  | (froms, node, label, tos) =>
                                let ig' := NatMap.add node (froms, label, tos) ig in
                                let ig'' := _updAdj tos (_addPred node) ig' in
                                _updAdj froms (_addSucc node) ig''
  end.


Definition insNode {A B : Type} (node : LNode A) (ig : IG A B) : IG A B :=
  match node with
  | (n, l) => add ([], n, l, []) ig
  end.

Definition insNodes {A B : Type} (nodes : list (LNode A)) (ig : IG A B) : IG A B :=
  fold_right insNode ig nodes.





Definition insEdge {A B : Type} (edge : LEdge B) (ig : IG A B) : IG A B :=
  match edge with
  | (from, to, l) =>
                    let (mcxt, ig') := IG_match from ig in
                    match mcxt with
                    | (Some (froms, _, label, tos)) => add (froms, from, label, (l, to) :: tos) ig'
                    | None => ig
                    end
  end.
                    
Definition insEdges {A B : Type} (edges : list (LEdge B)) (ig : IG A B) : IG A B :=
  fold_right insEdge ig edges.



Definition mkGraph {A B : Type} (nodes : list (LNode A)) (edges : list (LEdge B)) : IG A B :=
  insEdges edges (insNodes nodes IG_empty).

 
Definition labNodes {A B : Type} (ig : IG A B) : list (LNode A) :=
  map (fun '(v, (_, l, _)) => (v,l)) (NatMap.elements ig).








(* Make IGs visible  *)

Definition show_IG {A B : Type} (ig : IG A B) :=
  NatMap.elements ig. 

Definition show_Decomp {A B : Type} (d : Decomp A B) :=
  match d with
  | (mContext, x) => (mContext, show_IG x)
  end
.
