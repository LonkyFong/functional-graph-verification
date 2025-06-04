Require Import List.
Import ListNotations.

Require Import PeanoNat.

Require Import GraphVerification.src.util.NatSet.

(* Defining an algebraic_graph (AG) and its operations. There are only single edges.
It is based off of "Algebraic Graphs with Class (Functional Pearl)" by Andrey Mokhov. *)
Inductive AG (A : Type) : Type :=
    | Empty : AG A
    | Vertex : A -> AG A
    | Overlay : AG A -> AG A -> AG A
    | Connect : AG A -> AG A -> AG A.

Arguments Empty {A}.
Arguments Vertex {A}.
Arguments Overlay {A}.
Arguments Connect {A}.

(* For user-friendly input of AGs with numeric labels *)
Definition from_nat (n:nat) : AG nat :=
    Vertex n.
Coercion from_nat : nat >-> AG.



(* *** has more priority than +++ *)
Notation "ag1 +++ ag2" := (Overlay ag1 ag2) (at level 60, right associativity).
Notation "ag1 *** ag2" := (Connect ag1 ag2) (at level 59, right associativity).



(* Initially functions from the paper *)

Definition edge {A : Type} (a1 a2 : A) : AG A :=
    (Vertex a1) *** (Vertex a2).

Definition vertices {A : Type} (l : list A) : AG A :=
    fold_right Overlay Empty (map Vertex l).

Definition edges {A : Type} (l : list (A * A)) : AG A :=
    fold_right Overlay Empty (map (fun x => edge (fst x) (snd x)) l).

Definition clique {A : Type} (l : list A) : AG A :=
    fold_right Connect Empty (map Vertex l).

Definition makeGraph {A : Type} (vs : list A) (es : list (A * A)) : AG A :=
    Overlay (vertices vs) (edges es).


Definition path {A : Type} (l : list A) : AG A :=
    match l with
    | [] => Empty
    | [x] => Vertex x
    | _::xs => edges (combine l xs)
    end.

Definition circuit {A : Type} (l : list A) : AG A :=
    match l with
    | [] => Empty
    | x::_ => path (l ++ [x])
    end.

  
Definition star {A : Type} (x : A) (l : list A) : AG A :=
    Connect (Vertex x) (vertices l).


Fixpoint gmap {A A' : Type} (f : A -> A') (ag : AG A) : AG A' := 
    match ag with
    | Empty => Empty
    | Vertex x => Vertex (f x)
    | Overlay ag1 ag2 => Overlay (gmap f ag1) (gmap f ag2)
    | Connect ag1 ag2 => Connect (gmap f ag1) (gmap f ag2)
    end.


Definition mergeVertices {A : Type} (f : A -> bool) (v : A) (ag : AG A) : AG A :=
    gmap (fun x => if f x then v else x) ag.

Fixpoint toList {A : Type} (ag : AG A) : list A :=
    match ag with
    | Empty => []
    | Vertex x => [x]
    | Overlay ag1 ag2 => toList ag1 ++ toList ag2
    | Connect ag1 ag2 => toList ag1 ++ toList ag2
    end.

Fixpoint gmapVertex {A A' : Type} (f : AG A -> AG A') (ag : AG A) : AG A' :=
    match ag with
    | Empty => Empty
    | Vertex x => f (Vertex x)
    | Overlay ag1 ag2 => Overlay (gmapVertex f ag1) (gmapVertex f ag2)
    | Connect ag1 ag2 => Connect (gmapVertex f ag1) (gmapVertex f ag2)
    end.

Definition induce {A : Type} (f : A -> bool) (ag : AG A) : AG A :=
    gmapVertex (fun g' => match g' with
                          | Vertex x => if f x then Vertex x else Empty
                          | _ => g'
                          end) ag.


Definition removeVertex (x : nat) (ag : AG nat) : AG nat :=
    induce (fun y => negb (Nat.eqb x y)) ag.


Definition splitVertex {A : Type} (x : nat) (l : list nat) (ag : AG nat) : AG nat :=
    gmapVertex (fun g' => match g' with
                          | Vertex y => if Nat.eqb x y then vertices l else Vertex y
                          | _ => g'
                          end) ag.

Fixpoint removeEdge (x y : nat) (ag : AG nat) : AG nat :=
    match ag with
    | Empty => Empty
    | Vertex z => Vertex z
    | Overlay ag1 ag2 => Overlay (removeEdge x y ag1) (removeEdge x y ag2)
    | Connect ag1 ag2 => Overlay (Connect (removeVertex x ag1) ag2) (Connect ag1 (removeVertex y ag2))
    end.
    
    
  
Fixpoint transpose {A : Type} (ag : AG A) : AG A :=
    match ag with
    | Empty => Empty
    | Vertex x => Vertex x
    | Overlay ag1 ag2 => Overlay (transpose ag1) (transpose ag2)
    | Connect ag1 ag2 => Connect (transpose ag2) (transpose ag1)
    end.






(* Start defining own functions: *)

(* The set of nodes of the AG *)
Fixpoint AG_nodeSet (ag : AG nat) : NatSet.t := 
    let leftAndRight := fun (ag1 ag2 : AG nat) => NatSet.union (AG_nodeSet ag1) (AG_nodeSet ag2) in
    match ag with
    | Empty => NatSet.empty
    | Vertex x => NatSet.singleton x
    | Overlay ag1 ag2 => leftAndRight ag1 ag2
    | Connect ag1 ag2 => leftAndRight ag1 ag2
    end.

Definition AG_nodeAmount (ag : AG nat) : nat :=
    NatSet.cardinal (AG_nodeSet ag).


(* filters the provided set out of the list *)
Definition NatList_filterOutOf (remove : NatSet.t) (from : list nat) : list nat :=
    filter (fun x => negb (NatSet.mem x remove)) from.

(* Computes the set of nodes reachable from the provided set in a single step in the AG *)
Fixpoint _singleStep (from : NatSet.t) (ag : AG nat) : NatSet.t :=
    let leftAndRight := fun (ag1 ag2 : AG nat) (from : NatSet.t) => NatSet.union (_singleStep from ag1) (_singleStep from ag2) in
    match ag with
    | Empty => NatSet.empty
    | Vertex x => NatSet.empty
    | Overlay ag1 ag2 => leftAndRight ag1 ag2 from
    | Connect ag1 ag2 => NatSet.union (leftAndRight ag1 ag2 from) (
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

