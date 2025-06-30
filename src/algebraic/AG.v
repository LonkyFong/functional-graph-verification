Require Import List.
Import ListNotations.

Require Import PeanoNat.

Require Import GraphVerification.src.util.NatSet.

(** Defining an algebraic_graph (AG) and its operations. There are only single edges.
    It is based off of "Algebraic Graphs with Class (Functional Pearl)" by Andrey Mokhov. *)

Inductive AG (A : Type) : Type :=
    | AG_empty : AG A
    | AG_vertex : A -> AG A
    | AG_overlay : AG A -> AG A -> AG A
    | AG_connect : AG A -> AG A -> AG A.

Arguments AG_empty {A}.
Arguments AG_vertex {A}.
Arguments AG_overlay {A}.
Arguments AG_connect {A}.

(* For user-friendly input of AGs with numeric labels *)
Definition AG_from_nat (n : nat) : AG nat :=
    AG_vertex n.
Coercion AG_from_nat : nat >-> AG.



(* *** has more priority than +++ *)
Notation "ag1 +++ ag2" := (AG_overlay ag1 ag2) (at level 60, right associativity).
Notation "ag1 *** ag2" := (AG_connect ag1 ag2) (at level 59, right associativity).


(* Selection of construction primitives and polymorphic graph manipulators from the paper *)


Definition AG_vertices {A : Type} (l : list A) : AG A :=
    fold_right AG_overlay AG_empty (map AG_vertex l).

Definition AG_edge {A : Type} (a1 a2 : A) : AG A :=
    (AG_vertex a1) *** (AG_vertex a2).

Definition AG_edges {A : Type} (l : list (A * A)) : AG A :=
    fold_right AG_overlay AG_empty (map (fun x => AG_edge (fst x) (snd x)) l).

Definition AG_makeGraph {A : Type} (vs : list A) (es : list (A * A)) : AG A :=
    (AG_vertices vs) +++ (AG_edges es).


Fixpoint AG_transpose {A : Type} (ag : AG A) : AG A :=
    match ag with
    | AG_empty => AG_empty
    | AG_vertex x => AG_vertex x
    | ag1 +++ ag2 => AG_transpose ag1 +++ AG_transpose ag2
    | ag1 *** ag2 => AG_transpose ag2 *** AG_transpose ag1
    end.

Fixpoint AG_toList {A : Type} (ag : AG A) : list A :=
    match ag with
    | AG_empty => []
    | AG_vertex x => [x]
    | ag1 +++ ag2 => AG_toList ag1 ++ AG_toList ag2
    | ag1 *** ag2 => AG_toList ag1 ++ AG_toList ag2
    end.

Fixpoint AG_gmap {A A' : Type} (f : A -> A') (ag : AG A) : AG A' := 
    match ag with
    | AG_empty => AG_empty
    | AG_vertex x => AG_vertex (f x)
    | ag1 +++ ag2 => AG_gmap f ag1 +++ AG_gmap f ag2
    | ag1 *** ag2 => AG_gmap f ag1 *** AG_gmap f ag2
    end.


Definition AG_mergeVertices {A : Type} (f : A -> bool) (v : A) (ag : AG A) : AG A :=
    AG_gmap (fun x => if f x then v else x) ag.



Fixpoint AG_bind {A A' : Type} (f : A -> AG A') (ag : AG A) : AG A' :=
    match ag with
    | AG_empty => AG_empty
    | AG_vertex x => f x
    | ag1 +++ ag2 => AG_bind f ag1 +++ AG_bind f ag2
    | ag1 *** ag2 => AG_bind f ag1 *** AG_bind f ag2
    end.


Definition AG_induce {A : Type} (f : A -> bool) (ag : AG A) : AG A :=
    AG_bind (fun a => if f a then AG_vertex a else AG_empty) ag.


Definition AG_removeVertex (x : nat) (ag : AG nat) : AG nat :=
    AG_induce (fun y => negb (Nat.eqb x y)) ag.


Fixpoint AG_removeEdge (x y : nat) (ag : AG nat) : AG nat :=
    match ag with
    | AG_empty => AG_empty
    | AG_vertex z => AG_vertex z
    | ag1 +++ ag2 => AG_removeEdge x y ag1 +++ AG_removeEdge x y ag2
    | ag1 *** ag2 => ((AG_removeVertex x ag1) *** (AG_removeEdge x y ag2)) +++ ((AG_removeEdge x y ag1) *** (AG_removeVertex y ag2))
    end.










(** Start defining own functions (which will be verified): *)

(* The set of nodes of the AG. An AG could keep track of this internally to help performance *)
Fixpoint AG_nodeSet (ag : AG nat) : NatSet.t := 
    let leftAndRight := fun (ag1 ag2 : AG nat) => NatSet.union (AG_nodeSet ag1) (AG_nodeSet ag2) in
    match ag with
    | AG_empty => NatSet.empty
    | AG_vertex x => NatSet.singleton x
    | ag1 +++ ag2 => leftAndRight ag1 ag2
    | ag1 *** ag2 => leftAndRight ag1 ag2
    end.

(* The amount of _distinct_ nodes in the AG. An AG could keep track of this internally to help performance *)
Definition AG_nodeAmount (ag : AG nat) : nat :=
    NatSet.cardinal (AG_nodeSet ag).


(* filters the provided set out of the list *)
Definition NatList_filterOutOf (remove : NatSet.t) (from : list nat) : list nat :=
    filter (fun x => negb (NatSet.mem x remove)) from.

(* Computes the set of nodes reachable from the provided set in a single step in the AG *)
Fixpoint _singleStep (from : NatSet.t) (ag : AG nat) : NatSet.t :=
    let leftAndRight := fun (ag1 ag2 : AG nat) (from : NatSet.t) => NatSet.union (_singleStep from ag1) (_singleStep from ag2) in
    match ag with
    | AG_empty => NatSet.empty
    | AG_vertex x => NatSet.empty
    | ag1 +++ ag2 => leftAndRight ag1 ag2 from
    | ag1 *** ag2 => NatSet.union (leftAndRight ag1 ag2 from) (
                            let LHS := AG_nodeSet ag1 in
                            let RHS := AG_nodeSet ag2 in 
                            if NatSet.is_empty (NatSet.inter LHS from) then NatSet.empty else RHS)
    end.

(* Computes a list of the set of reachable nodes until it does not grow (kept track by visited).
    Assumes that all of from are in the AG *)
Fixpoint _upToNStepsCap_rec  (from visited : NatSet.t) (ag : AG nat) (n : nat) : list NatSet.t :=
    match n with
    | 0 => []
    | S n' => from ::
                let next := _singleStep from ag in
                let nextVisited := NatSet.union visited next in 
                if NatSet.equal visited nextVisited then [] else
                    _upToNStepsCap_rec  next nextVisited ag n'
    end.

(* Caller for "_upToNStepsCap_rec" *)
Definition _upToNStepsCap (from : NatSet.t) (ag : AG nat) (n : nat) : list NatSet.t :=
    let trimmedFrom := NatSet.inter from (AG_nodeSet ag) in
    _upToNStepsCap_rec trimmedFrom trimmedFrom ag (S n).

(* Combines result of "_upToNStepsCap" to make a real BFS *)
Definition AG_BFS (from : list nat) (ag : AG nat) :=
    fold_right (fun next acc => NatSet.elements next ++ (NatList_filterOutOf next acc)) [] (_upToNStepsCap (NatSet_fromList from) ag (AG_nodeAmount ag)).

