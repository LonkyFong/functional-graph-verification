Require Import List.
Import ListNotations.
Require Import Bool.
Require Import Nat.

Require Import Coq.Arith.PeanoNat.

Require Import Coq.Lists.ListSet.
Require Import Coq.Arith.EqNat.

Require Import Coq.Arith.Peano_dec.
Require Import Recdef.

Require Import MyProject.project.util.NatSet.

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
Notation "ag1 --> ag2" := (Connect ag1 ag2) (at level 59, right associativity).




(* The first part of this file is just the code from the paper copied to coq,
later on (around l.200) it becomes more experimental *)



Definition edge {A : Type} (a1 a2 : A) : AG A :=
    Connect (Vertex a1) (Vertex a2).

Definition vertices {A : Type} (l : list A) : AG A :=
    fold_right Overlay Empty (map Vertex l).

Definition edges {A : Type} (l : list (A * A)) : AG A :=
    fold_right Overlay Empty (map (fun x => edge (fst x) (snd x)) l).

Definition clique {A : Type} (l : list A) : AG A :=
    fold_right Connect Empty (map Vertex l).

Compute clique [1; 2; 3; 4].

Definition makeGraph {A : Type} (vs : list A) (es : list (A * A)) : AG A :=
    Overlay (vertices vs) (edges es).



Check makeGraph [1; 2; 3] [(1, 2); (2, 3)].
Check 1 *** (2 +++ 3).
Compute 1 *** (2 +++ 3) +++ 2 *** 3 = clique[1; 2; 3].


Definition path {A : Type} (l : list A) : AG A :=
    match l with
    | [] => Empty
    | [x] => Vertex x
    | _::xs => edges (combine l xs)
    end.

Compute path [1; 2; 3; 4].


Definition circuit {A : Type} (l : list A) : AG A :=
    match l with
    | [] => Empty
    | x::_ => path (l ++ [x])
    end.

Compute circuit [1; 2; 3; 4].
  
Definition star {A : Type} (x : A) (l : list A) : AG A :=
    Connect (Vertex x) (vertices l).

Compute star 1 [2; 3; 4].


Fixpoint gmap {A A' : Type} (f : A -> A') (ag : AG A) : AG A' := 
    match ag with
    | Empty => Empty
    | Vertex x => Vertex (f x)
    | Overlay ag1 ag2 => Overlay (gmap f ag1) (gmap f ag2)
    | Connect ag1 ag2 => Connect (gmap f ag1) (gmap f ag2)
    end.

Compute gmap (fun x => x + 1) (1 *** 2 +++ 3 *** 4).

Definition mergeVertices {A : Type} (f : A -> bool) (v : A) (ag : AG A) : AG A :=
    gmap (fun x => if f x then v else x) ag.

Fixpoint toList {A : Type} (ag : AG A) : list A :=
    match ag with
    | Empty => []
    | Vertex x => [x]
    | Overlay ag1 ag2 => toList ag1 ++ toList ag2
    | Connect ag1 ag2 => toList ag1 ++ toList ag2
    end.

Compute toList (1 *** 2 +++ 3 *** 4).


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


Compute induce (fun x => eqb  x  1) (1 *** 2 +++ 3 *** 4 +++ 1 *** 2).

Definition removeVertex (x : nat) (ag : AG nat) : AG nat :=
    induce (fun y => negb (eqb x y)) ag.

Compute removeVertex 1 (1 *** 2 +++ 3 *** 4 +++ 1 *** 2).



Definition splitVertex {A : Type} (x : nat) (l : list nat) (ag : AG nat) : AG nat :=
    gmapVertex (fun g' => match g' with
                          | Vertex y => if eqb x y then vertices l else Vertex y
                          | _ => g'
                          end) ag.



Compute splitVertex 1 [0; 1] (1 *** (2 +++ 3)).

Fixpoint removeEdge (x y : nat) (ag : AG nat) : AG nat :=
    match ag with
    | Empty => Empty
    | Vertex z => Vertex z
    | Overlay ag1 ag2 => Overlay (removeEdge x y ag1) (removeEdge x y ag2)
    | Connect ag1 ag2 => Overlay (Connect (removeVertex x ag1) ag2) (Connect ag1 (removeVertex y ag2))
    end.
    
    
  
Compute removeEdge 1 2 (1 *** 2 +++ 3 *** 4).



Fixpoint transpose {A : Type} (ag : AG A) : AG A :=
    match ag with
    | Empty => Empty
    | Vertex x => Vertex x
    | Overlay ag1 ag2 => Overlay (transpose ag1) (transpose ag2)
    | Connect ag1 ag2 => Connect (transpose ag2) (transpose ag1)
    end.

















(* Here, I start deviating from the paper: *)


(* These functions assume no overlapping node labels. It thinks that 1 *** 1 has 2 nodes *)

Fixpoint AG_toList {A : Type} (ag : AG A) : list A :=
    match ag with
    | Empty => []
    | Vertex x => [x]
    | Overlay ag1 ag2 => AG_toList ag1 ++ AG_toList ag2
    | Connect ag1 ag2 => AG_toList ag1 ++ AG_toList ag2
    end.


Compute AG_toList (1 *** 2 +++ 3 *** 4).
Compute AG_toList (1 *** 2 +++ 1 *** 2).
Compute AG_toList (1 *** 1).
Compute AG_toList (1 +++ 1).



Fixpoint countNodes {A : Type} (ag : AG A) : nat :=
    match ag with
    | Empty => 0
    | Vertex x => 1
    | Overlay ag1 ag2 => countNodes ag1 + countNodes ag2
    | Connect ag1 ag2 => countNodes ag1 + countNodes ag2
    end.

Fixpoint countEdges {A : Type} (ag : AG A) : nat :=
    match ag with
    | Empty => 0
    | Vertex x => 0
    | Overlay ag1 ag2 => countEdges ag1 + countEdges ag2
    | Connect ag1 ag2 => countEdges ag1 + countEdges ag2 + countNodes ag1 * countNodes ag2
    end.








(* This a somewhat analogous to DFS *)
(* A little magical, since we are using the returned list as a output list as well as a set *)
Fixpoint searchGraphUnique (ag : AG nat) (s : set nat) : (list nat) :=
    match ag with
    | Empty => []
    | Vertex x => if set_mem eq_nat_dec x s then [] else [x]
    | Overlay ag1 ag2 => match searchGraphUnique ag1 s with
                        | ret => ret ++ searchGraphUnique ag2 (set_union eq_nat_dec s ret)
                        end
    | Connect ag1 ag2 => match searchGraphUnique ag1 s with
                        | ret => ret ++ searchGraphUnique ag2 (set_union eq_nat_dec s ret)
                        end
    end.


Compute searchGraphUnique (1 *** 2 +++ 3 *** 4) [].
Compute searchGraphUnique (1 *** 2 +++ 1 *** 2) [].
Compute searchGraphUnique (1 *** 1) [].
Compute searchGraphUnique (1 +++ 1) [].

Compute searchGraphUnique (1 *** 2 +++ 2 *** 3 +++ 1 *** 3) [].











Fixpoint listEqual (l1 l2 : list nat) : bool :=
  match l1, l2 with
    | [], [] => true
    | x :: xs, y :: ys => if eq_nat_dec x y then listEqual xs ys else false
    | _, _ => false
  end.


Fixpoint filterOutOf (remove from : list nat) : list nat :=
  match from with
    | [] => []
    | x :: xs => if existsb (fun y => x =? y) remove then filterOutOf remove xs else x :: filterOutOf remove xs
  end.

(* When getting rid of the fuel, the function is alwas gbeing called on a (bigger list (max amount on nodes in the graph) and a samller graph) these should be summable together. No lexographic order business *) 
Fixpoint canReachFrom_fuled (ag : AG nat) (acc : list nat) (fuel : nat) : list nat :=
    match fuel with
        | 0 => acc
        | S fuel' => match ag with
                        | Empty => acc
                        | Vertex x => acc
                        | Overlay ag1 ag2 => let result := canReachFrom_fuled ag1 acc fuel' in 
                                                let result' := canReachFrom_fuled ag2 result fuel' in 
                                                if listEqual acc result' then acc else canReachFrom_fuled ag result' fuel' (*actually, result' is never smaller*)

                        | Connect ag1 ag2 =>   let result := canReachFrom_fuled ag1 acc fuel' in 
                                                let result' := canReachFrom_fuled ag2 result fuel' in
                                                let LHS := searchGraphUnique ag1 [] in

                                                let RHS := searchGraphUnique ag2 [] in
                                                let result'' := if existsb (fun x => (set_mem eq_nat_dec x LHS)) result' then result' ++ filterOutOf result' RHS else result' in  
                                                if listEqual acc result'' then acc else canReachFrom_fuled ag result'' fuel'
                        end
    end.

Compute canReachFrom_fuled (Vertex 1) [1] 10.
Compute canReachFrom_fuled ((1 *** 2 +++ 3 *** 4) +++ (2 *** 3)) [1] 7.
Compute canReachFrom_fuled ((3 *** 4) +++ (1 *** 2 +++ 2 *** 3)) [1] 7.
Compute canReachFrom_fuled ((1 *** 2) +++ (3 *** 4)) [1; 3] 7.





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



Definition NatList_filterOutOf (remove : NatSet.t) (from : list nat) : list nat :=
    filter (fun x => negb (NatSet.mem x remove)) from.

    


(* Definition NatList_remove_duplicates (l : list nat) : list nat :=
  fold_left (fun acc next => if existsb (fun y => y =? next) acc then acc else acc ++ [next]) l nil. *)
  


(* Definition NatList_union (l1 l2 : list nat) :=
    l1 ++ NatList_remove_duplicates (NatList_filterOutOf l1 l2). *)

(* This is pretty promising :) *)

Fixpoint _singleStep (ag : AG nat) (from : NatSet.t) : NatSet.t :=
let leftAndRight := fun (ag1 ag2 : AG nat) (from : NatSet.t) => NatSet.union (_singleStep ag1 from) (_singleStep ag2 from) in
 match ag with
        | Empty => NatSet.empty
        | Vertex x => NatSet.empty
        | Overlay ag1 ag2 => leftAndRight ag1 ag2 from

        | Connect ag1 ag2 => NatSet.union (leftAndRight ag1 ag2 from) (
                                let LHS := AG_nodeSet ag1 in
                                let RHS := AG_nodeSet ag2 in 
                                if NatSet.is_empty (NatSet.inter LHS from) then NatSet.empty else RHS
        )
                  
    end.

Definition _singleStep_caller (ag : AG nat) (from : list nat) : list nat :=
    NatSet.elements (_singleStep ag (NatSet_fromList from)).

Compute _singleStep_caller (Vertex 1) [1]. 
Compute _singleStep_caller ((1 *** 2 +++ 3 *** 4) +++ (2 *** 3)) [1].
Compute _singleStep_caller ((3 *** 4) +++ (1 *** 2 +++ 2 *** 3)) [1].
Compute _singleStep_caller ((1 *** 2) +++ (3 *** 4)) [1; 3].


(* This is not needed, as using it repeatedly is slow *)
Fixpoint canReachInNorFewerSteps (ag : AG nat) (from : NatSet.t) (n : nat) : list (NatSet.t) :=
  match n with
    | 0 => []
    | S n' => from :: canReachInNorFewerSteps ag (_singleStep ag from) n'
  end.

Definition canReachInNorFewerSteps_caller (ag : AG nat) (from : list nat) (n : nat) : list (list nat) :=
    map NatSet.elements (canReachInNorFewerSteps ag (NatSet_fromList from) n).

Compute canReachInNorFewerSteps_caller (Vertex 1) [1] 3.
(* Notice, that when we have a cycle, the list is infinite *)
Compute canReachInNorFewerSteps_caller ((1 *** 2 +++ 3 *** 4) +++ (2 *** 3 +++ 4 *** 1)) [1] 6. 
Compute canReachInNorFewerSteps_caller ((3 *** 4) +++ (1 *** 2 +++ 2 *** 3)) [1] 4.   
Compute canReachInNorFewerSteps_caller ((1 *** 2) +++ (3 *** 4)) [1; 3] 10.



Fixpoint _upToNStepsCap (ag : AG nat) (from visited : NatSet.t) (n : nat) : list NatSet.t :=
  match n with
    | 0 => []
    | S n' => from ::
            let next := _singleStep ag from in
            let nextVisited := NatSet.union visited next in 
            if NatSet.equal visited nextVisited then [] else
                 _upToNStepsCap ag next nextVisited  n'
  end.



Definition _upToNStepsCapCaller (ag : AG nat) (from : NatSet.t) (n : nat) : list NatSet.t :=
    let trimmedFrom := NatSet.inter from (AG_nodeSet ag) in
    _upToNStepsCap ag trimmedFrom trimmedFrom (S n).

Definition canReachInNStepsListCapped_caller2 (ag : AG nat) (from : list nat) (n : nat) : list (list nat) :=
    map NatSet.elements (_upToNStepsCapCaller ag (NatSet_fromList from) n).

Compute canReachInNStepsListCapped_caller2 (Vertex 1) [1] 10.
Compute canReachInNStepsListCapped_caller2 ((1 *** 2 +++ 3 *** 4) +++ (2 *** 3)) [1] 10.
Compute canReachInNStepsListCapped_caller2 ((3 *** 4) +++ (1 *** 2 +++ 2 *** 3)) [1] 1000.   
Compute canReachInNStepsListCapped_caller2 ((1 *** 2) +++ (3 *** 4)) [1; 3] 0.


Definition AG_BFS (ag : AG nat) (from : list nat) :=
    fold_right (fun next acc => NatSet.elements next ++ (NatList_filterOutOf next acc)) [] (_upToNStepsCapCaller ag (NatSet_fromList from) (AG_nodeAmount ag)).

Compute AG_BFS (Vertex 1) [1].
Compute AG_BFS ((1 *** 2 +++ 3 *** 4) +++ (2 *** 3)) [1].
Compute AG_BFS ((3 *** 4) +++ (1 *** 2 +++ 2 *** 3)) [1].   
Compute AG_BFS ((1 *** 2) +++ (3 *** 4)) [1; 3].

