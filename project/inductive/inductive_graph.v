Require Import String.
Require Import Coq.Arith.Arith.
Open Scope string_scope.

Require Import List.
Require Import Bool.
Import ListNotations.

(* This file defines an inductive graph using maps like Erwig *)
(* Note that A is the node label type and B is the edge label type *)
(* At the moment, there are only the "MINIMAL" implementations  *)

(*
(* TODO: for verification, I either write algebraic specifications using these (no need for "well-formedness"),
or I "implement" all of them an show that they are correct for relational graphs and then show _isomorphism_ (here, yes need for "well-formedness")
  for the translation to relational graphs, I would formally need to show "complete" and "correctness" (like they do for elements in BST)
  I would also need to implement "at least some of these operations" for relational graphs *)
class Graph gr where
  {-# MINIMAL empty, isEmpty, match, mkGraph, labNodes #-}

  -- | An empty 'Graph'.
  empty     :: gr a b

  -- | True if the given 'Graph' is empty.
  isEmpty   :: gr a b -> Bool

  -- | Decompose a 'Graph' into the 'MContext' found for the given node and the
  -- remaining 'Graph'.
  match     :: node -> gr a b -> Decomp gr a b

  -- | Create a 'Graph' from the list of 'LNode's and 'LEdge's.
  --
  --   For graphs that are also instances of 'DynGraph', @mkGraph ns
  --   es@ should be equivalent to @('insEdges' es . 'insNodes' ns)
  --   'empty'@.
  mkGraph   :: [LNode a] -> [LEdge b] -> gr a b

  -- | A list of all 'LNode's in the 'Graph'.
  labNodes  :: gr a b -> [LNode a]

  -- | Decompose a graph into the 'Context' for an arbitrarily-chosen 'Node'
  -- and the remaining 'Graph'.
  matchAny  :: gr a b -> GDecomp gr a b

  -- | The number of 'Node's in a 'Graph'.
  noNodes   :: gr a b -> Int

  -- | The minimum and maximum 'Node' in a 'Graph'.
  nodeRange :: gr a b -> (Node,Node)

  -- | A list of all 'LEdge's in the 'Graph'.
  labEdges  :: gr a b -> [LEdge b]
  *)


(* https://rocq-prover.org/doc/v8.9/stdlib/Coq.FSets.FMapList.html *)
Require Import Coq.FSets.FMapInterface.
Require Import Coq.FSets.FMapList.
(* Require Import Coq.FSets.FMapAVL. *)
Require Import Coq.FSets.FMapFacts.
Require Import Coq.Structures.OrderedTypeEx.

Definition node := Nat_as_OT.t.


Module NatMap := FMapList.Make(Nat_as_OT).
(* Module NatMap := FMapAVL.Make(Nat_as_OT). *)


Open Scope nat_scope.

(* In case, I want to go polymorphic some day *)
(* Definition Adj (A : Type) := list (A * node).

Definition Context (A B : Type) : Type :=
    (Adj B * node * A * Adj B).

Definition MContext (A B : Type) : Type :=
    option (Context A B).

Definition Decomp (Graph : Type -> Type -> Type) (A B : Type) : Type :=
  (MContext A B * Graph A B). *)




Definition Adj' (B : Type) := NatMap.t B.

(* No node needed, since the node is the key *)
Definition Context' (A B : Type) : Type :=
  (Adj' B * A * Adj' B).

Definition MContext' (A B : Type) : Type :=
    option (Context' A B).



Definition bind {A B : Type} (x : option A) (f : A -> option B) : option B :=
  match x with
  | None => None
  | Some a => f a
  end.


Require Import Coq.FSets.FSetList.
Require Import Coq.FSets.FSetEqProperties.

Module NatSet := FSetList.Make(Nat_as_OT).
Print FSetEqProperties.
Module NatSetProperties := FSetEqProperties.EqProperties(NatSet).




(* Returns None, if there are duplicates *)
Definition set_from_list (l : list node) : option NatSet.t :=
  fold_right (fun (k : node) (acc : option NatSet.t) =>
                bind acc (fun (acc : NatSet.t) => if NatSet.mem k acc then None else Some (NatSet.add k acc))
              ) (Some NatSet.empty) l.

  

Definition IG_map_out_keys {A B : Type} (IG_data : NatMap.t (Context' A B)) : option NatSet.t :=
  set_from_list (
    concat (
      map (fun (X : (node * Context' A B)) =>
            match (snd X) with
              | (_, _, out_map) => map fst (NatMap.elements out_map)
            end
          )
      (NatMap.elements IG_data)
    )
  )
.


Definition IG_map_in_keys {A B : Type} (IG_data : NatMap.t (Context' A B)) : option NatSet.t :=
  set_from_list (
    concat (
      map (fun (X : (node * Context' A B)) =>
            match (snd X) with
              | (in_map, _, _) => map fst (NatMap.elements in_map)
            end
          )
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
  

Definition IG_valid_cond {A B : Type} (IG_data : NatMap.t (Context' A B)) : Prop :=
  IG_valid_cond_fun IG_data = true.

Definition IG_data_unsafe (A B : Type) : Type :=
  NatMap.t (Context' A B).
  
(* Map instead of list *)
Record IG (A B : Type) := {
  IG_data : IG_data_unsafe A B;
  IG_valid : IG_valid_cond IG_data
}.

Arguments IG_data {A B}.
Arguments IG_valid {A B}.



Definition Decomp' (A B : Type) : Type :=
  (MContext' A B * IG A B).





(* Start defining functionality: *)
Definition empty {A B : Type} : IG A B.
Proof.
  refine ({|
    IG_data := NatMap.empty (Context' A B);
    IG_valid := _
  |}).
  unfold IG_valid_cond.
  unfold IG_valid_cond_fun.
  simpl.
  pose proof NatSetProperties.union_subset_equal.
  apply H.
  apply NatSetProperties.subset_refl.
Defined.



Definition isEmpty {A B : Type} (x : IG A B) : bool :=
  NatMap.is_empty x.(IG_data).

Compute isEmpty empty.


(* Here start the helper functions for "matsh". match is a reserved keyword by coq.... *)

(* Applies a function to a map entry if it exists quickly *)
Definition update_entry {A B : Type} (n : node) (f : Context' A B -> Context' A B) (x : IG_data_unsafe A B) : IG_data_unsafe A B :=
  match NatMap.find n x with
    | Some v => NatMap.add n (f v) x
    | None => x
  end.



Definition clean_up_helper {A B : Type} (n : node) (outs_with_n ins_with_n : list node) (x : IG_data_unsafe A B) : IG_data_unsafe A B :=
  (* Loop over ingoing edges of removed node to update the outgoing of all of those to not have n anymore *)
  let x' := fold_right (fun (elem : node) (acc : IG_data_unsafe A B) =>
    update_entry elem (fun con => match con with
                                  | (in_map', key', out_map') => (in_map', key', NatMap.remove n out_map')
                                  end)
    acc) x outs_with_n in
  (* Loop over outgoing edges of removed node to update the ingoing of all of those to not have n anymore *)
  fold_right (fun (elem : node) (acc : IG_data_unsafe A B) =>
    update_entry elem (fun con => match con with
                                  | (in_map', key', out_map') =>  (NatMap.remove n in_map', key', out_map')
                                  end)
    acc) x' ins_with_n
.


Definition clean_up {A B : Type} (n : node) (context : Context' A B) (x : IG_data_unsafe A B) : IG_data_unsafe A B :=
  match context with
    | (in_map, _, out_map) =>
  
      let outs_with_n := map fst (NatMap.elements in_map) in
      let ins_with_n := map fst (NatMap.elements out_map) in
      clean_up_helper n outs_with_n ins_with_n (NatMap.remove n x)
  
  end.



Definition matsh {A B : Type} (n : node) (x : IG A B) : Decomp' A B.
Proof.
  pose
  match NatMap.find n x.(IG_data) with
  | None => (None, empty.(IG_data))
  | Some context as mContext => (mContext, clean_up n context x.(IG_data)) 
  end as intermediate_computation.
  split.
  - destruct intermediate_computation as [mContext x']. apply mContext.
  - destruct intermediate_computation as [mContext x'].
  refine ({|
    IG_data := x';
    IG_valid := _
  |}).
  unfold IG_valid_cond.
  unfold IG_valid_cond_fun.

Admitted.






Definition LNode (A : Type) : Type := (node * A).
Definition LEdge (B : Type) : Type := (node * node * B).

(* Here start the helper functions for "mkGraph" *)


(* This is the "&" constructor, but it has to be defined as a function, since it is too advanced *)
Definition add {A B : Type} (n : node) (node : Context' A B) (x : IG A B) : IG A B.
Proof.
  refine ({|
    IG_data := NatMap.add n node x.(IG_data);
    IG_valid := _
  |}).
Admitted.




Definition insNode {A B : Type} (node : LNode A) (x : IG A B) : IG A B.
Proof.
  refine ({|
    IG_data :=   match node with
    | (v, l) => (add v (NatMap.empty B, l, NatMap.empty B) x).(IG_data)
    end;
    IG_valid := _
  |}).
Admitted.



Definition insNodes {A B : Type} (nodes : list (LNode A)) (x : IG A B) : IG A B :=
  fold_right insNode x nodes.





Definition insEdge {A B : Type} (edge : LEdge B) (x : IG A B) : IG A B.
Proof.
  refine ({|
    IG_data := match edge with
    | (v,w,l) =>  update_entry v (fun con => match con with
                  | (in_map, key', out_map) => (in_map, key', NatMap.add w l out_map)
                  end)
                  (
                  (* Now update the other side of the edge *)
                  update_entry w (fun con => match con with
                  | (in_map, key', out_map) => (NatMap.add v l in_map, key', out_map)
                  end)
                  x.(IG_data)
                  )
    end;
    IG_valid := _
  |}).
Admitted.



Definition insEdges {A B : Type} (edges : list (LEdge B)) (x : IG A B) : IG A B :=
  fold_right insEdge x edges.



Definition mkGraph {A B : Type} (nodes : list (LNode A)) (edges : list (LEdge B)) : IG A B :=
  insEdges edges (insNodes nodes empty).


 
Definition labNodes {A B : Type} (x : IG A B) : list (LNode A) :=
  map (fun X => match X with | (v, (_, l, _)) => (v,l) end) (NatMap.elements x.(IG_data)).














Definition show_IG {A B : Type} (x : IG A B) :=
  map (fun X => match X with | (k, (in_m, lab, out_m)) => (k, (NatMap.elements in_m, lab, NatMap.elements out_m)) end) (NatMap.elements x.(IG_data)).

Definition show_Context {A B : Type} (con : Context' A B) :=
  match con with
  | (in_map, key, out_map) => (NatMap.elements in_map, key, NatMap.elements out_map)
  end.


(* Definition option_map (A B:Type) (f:A->B) (o : option A) : option B :=
  match o with
    | Some a => @Some B (f a)
    | None => @None B
  end. *)


Definition show_MContext {A B : Type} (mContext : MContext' A B) :=
  option_map (fun con => show_Context con) mContext.


Definition show_MContext_lame {A B : Type} (mContext : MContext' A B) :=
  match mContext with
  | None => None
  | Some con => Some (show_Context con)
  end.


Definition show_Decomp {A B : Type} (d : Decomp' A B) :=
  match d with
  | (mContext, x) => (show_MContext mContext, show_IG x)
  end.



Compute show_IG (mkGraph [(1, 1); (2, 2); (3, 3)] [(1, 2, 1); (2, 3, 2); (3, 1, 3)]).

Definition my_basic_graph := mkGraph [(1, "a"); (2, "b"); (3, "c")] [(1, 2, "edge1"); (2, 3, "edge2"); (3, 1, "edge3")].

(* Here come the tests for each defined function (that is in the graph class): *)

Compute show_IG empty.

Compute isEmpty empty.
Compute isEmpty my_basic_graph.

Compute show_Decomp (matsh 2 my_basic_graph).

Compute show_IG (mkGraph [(1, "a"); (2, "b"); (3, "c")] [(1, 2, "edge1"); (2, 3, "edge2"); (3, 1, "edge3")]).

Compute labNodes my_basic_graph.


(* Helpers for proving correctness: *)
Definition lookup {X Y : Type} (n : node) (ig : IG X Y) : option X :=
  option_map (fun c => match c with (_, label, _) => label end) (NatMap.find n ig.(IG_data)).
  




(* Here, I try out various equational specifications of an IG: *)

Check empty.
(* IG ?A ?B *)

Check isEmpty.
(* IG ?A ?B -> bool. *)

Check matsh.
(* node -> IG ?A ?B -> Decomp' ?A ?B. *)

Print Decomp'.
(* (MContext' A B * IG A B) *)

Print MContext'.
(* option (Context' A B) *)

Print Context'.
(* (Adj' B * A * Adj' B) *)

Print Adj'.
(* NatMap.t B *)

Print LNode.
(* (node * ?A) *)

Print LEdge.
(* (node * node * ?B) *)

Check mkGraph.
(* list (LNode ?A) -> list (LEdge ?B) -> IG ?A ?B. *)

Check labNodes.
(* IG ?A ?B -> list (LNode ?A). *)


Theorem spec1 : forall A B, isEmpty (@empty A B) = true.
Proof.
  intros. compute. reflexivity.
Qed.

Theorem spec2 : forall (A B : Type) (nl : list (LNode A)) (el : list (LEdge B)), labNodes (mkGraph nl el) = nl.
Proof.
  intros. compute.
Admitted.

Theorem spec3 : forall (A B : Type) (n : node), matsh n (@empty A B) = (None, empty).
Proof.
  intros. compute.
Admitted.

Theorem spec4 : forall (A B : Type) (n : LNode A) (nl : list (LNode A)) (el : list (LEdge B)), 
  In n nl -> exists map1 map2, matsh (fst n) (mkGraph nl el) =
  (Some ((map1), snd n, (map2)), mkGraph (filter (fun '(idx, lab) => negb (fst n =? idx)) nl) (filter (fun '(to, from, lab) => negb ((to =? fst n) || (from =? fst n))) el)).
(* This is not even a complete specification and it looks like a nightmare to prove... *)

Theorem spec5 : forall (A B : Type) (n : LNode A) (nl : list (LNode A)) (el : list (LEdge B)), 
  not (In n nl) -> matsh (fst n) (mkGraph nl el) = (None, mkGraph nl el).

