Require Import Arith.
Require Import String.
Open Scope string_scope.

Require Import Bool.
Require Import List.
Import ListNotations.

Require Import GraphVerification.src.util.NatMap.
Require Import GraphVerification.src.util.NatSet.
Require Import GraphVerification.src.util.util.

Open Scope nat_scope.

(* Defining an inductive_graph (IG) and its operations.
It is based off of "Inductive graphs and functional graph algorithms" by Martin Erwig.
It tries to mirror the FGL (functional graph library) whenever possible,
but most importantly only treats one of the multiple implementations of the inductive graph class.

Minimal operations are:
  empty, isEmpty, match, mkGraph, labNodes
Further down, further derived operations are defined:
  matchAny, noNodes, nodeRange, labEdges
*) 


Definition Adj (B : Type) := list (B * Node). 

Definition Context (A B : Type) : Type :=
    (Adj B * Node * A * Adj B).

Definition MContext (A B : Type) : Type :=
    option (Context A B).


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

(* These are here for now, as all theory files use them *)
Ltac destruct_context c := destruct c as [[[froms node] label] tos].
Ltac destruct_contextt c := destruct c as [[[fromss nodee] labell] toss].
Ltac destruct_contexttt c := destruct c as [[[fromsss nodeee] labelll] tosss].
Ltac destruct_context' c' := destruct c' as [[froms' label'] tos'].
Ltac destruct_contextt' c' := destruct c' as [[fromss' labell'] toss'].

Ltac destruct_edge e := destruct e as [[from to] el].


(* Here start the helper functions for IG_match *)


(* Applies a function to a map entry if it exists quickly *)
Definition _updateEntry {A B : Type} (node : Node) (f : Context' A B -> Context' A B) (ig : IG A B) : IG A B := 
    match NatMap.find node ig with
    | Some v => NatMap.add node (f v) ig
    | None => ig
    end.



Definition _addSucc {A B : Type} (node : Node) (label : B) (context' : Context' A B) : Context' A B :=
    let '(froms, l, tos) := context' in (froms, l, (label, node) :: tos).
  
Definition _addPred {A B : Type} (node : Node) (label : B) (context' : Context' A B) : Context' A B :=
    let '(froms, l, tos) := context' in ((label, node) :: froms, l, tos).

Definition _clearSucc {A B : Type} (node : Node) (context' : Context' A B) : Context' A B :=
    let '(froms, label, tos) := context' in (froms, label, filter (fun '(_, n) => negb (n =? node)) tos).

Definition _clearPred {A B : Type} (node : Node) (context' : Context' A B) : Context' A B :=
    let '(froms, label, tos) := context' in (filter (fun '(_, n) => negb (n =? node)) froms, label, tos).



Definition _updAdj {A B : Type} (adj : Adj B) (f : B -> Context' A B -> Context' A B) (ig : IG A B) : IG A B :=
    fold_right (fun '(l, n) (acc : IG A B) => _updateEntry n (f l) acc) ig adj.  


Definition _cleanSplit {A B : Type} (node : Node) (context' : Context' A B) (ig : IG A B) : Context A B * IG A B :=
    let '(froms, label, tos) := context' in
    let rmLoops := filter (fun '(_, n) => negb (n =? node)) in

    let froms' := rmLoops froms in
    let tos' := rmLoops tos in
    let context := (froms', node, label, tos (*no '*)) in
    
    let ig' := _updAdj froms' (fun x y => _clearSucc node y) ig in 
    let ig'' := _updAdj tos' (fun x y => _clearPred node y) ig' in
    (context, ig'')
    .


Definition IG_match {A B : Type} (node : Node) (ig : IG A B) : Decomp A B :=
    match NatMap.find node ig with
    | None => (None, ig)
    | Some context' => match _cleanSplit node context' (NatMap.remove node ig) with
                        | (context, ig') => (Some context, ig')
                        end
    end.




(* Here start the helper functions for IG_mkGraph *)


(* This is the "&" constructor from the paper, defined here as a function, as it does more than mere pattern matching *)
(* Does nothing, if the node already exists *)
(* In case neighbours do not exist, the entries are ignored (updateEntry does not find them) *)
Definition IG_and {A B : Type} (context : Context A B) (ig : IG A B) : IG A B :=
    let '(froms, node, label, tos) := context in

    if NatMap.mem node ig then ig else
    let ig' := NatMap.add node (froms, label, tos) ig in
    let ig'' := _updAdj tos (_addPred node) ig' in
    _updAdj froms (_addSucc node) ig''.


Definition _insNode {A B : Type} (node : LNode A) (ig : IG A B) : IG A B :=
    let '(n, l) := node in
    IG_and ([], n, l, []) ig.

Definition _insNodes {A B : Type} (nodes : list (LNode A)) (ig : IG A B) : IG A B :=
    fold_right _insNode ig nodes.



Definition _insEdge {A B : Type} (edge : LEdge B) (ig : IG A B) : IG A B :=
    let '(from, to, l) := edge in
    let (mcxt, ig') := IG_match from ig in

    match mcxt with
    | (Some (froms, _, label, tos)) => IG_and (froms, from, label, (l, to) :: tos) ig'
    | None => ig
    end.


Definition _insEdges {A B : Type} (edges : list (LEdge B)) (ig : IG A B) : IG A B :=
    fold_right _insEdge ig edges.


Definition IG_mkGraph {A B : Type} (nodes : list (LNode A)) (edges : list (LEdge B)) : IG A B :=
    _insEdges edges (_insNodes nodes IG_empty).

 
Definition IG_labNodes {A B : Type} (ig : IG A B) : list (LNode A) :=
    map (fun '(v, (_, l, _)) => (v,l)) (NatMap.elements ig).




(* Now come some derived operations, which are also part of the graph class in FGL *)

Definition IG_matchAny {A B : Type} (ig : IG A B) : Decomp A B :=
    match IG_labNodes ig with
    | [] => (None, ig)
    | node :: nodes => IG_match (fst node)  ig
    end.
  


Definition IG_noNodes {A B : Type} (ig : IG A B) : nat :=
    length (IG_labNodes ig).

(* Gets the first item of the list passed in directly, to avoid the need for a default value *)
Definition _minimum (n : nat) (l : list nat) : nat :=
    fold_right min n l.

(* Gets the first item of the list passed in directly, to avoid the need for a default value *)
Definition _maximum (n : nat) (l : list nat) : nat :=
    fold_right max n l.

(* This is a little different from FGL *)
Definition IG_nodeRange {A B : Type} (ig : IG A B) : Node * Node :=
    match map fst (IG_labNodes ig) with
    | [] => (0, 0)
    | node :: nodes => (_minimum node nodes, _maximum node nodes)
    end.



Definition IG_labEdges {A B : Type} (ig : IG A B) : list (LEdge B) :=
    fold_right (fun '(node, (_, _, tos)) acc => map (fun '(l, to) => (node, to, l)) tos ++ acc) [] (NatMap.elements ig). 
