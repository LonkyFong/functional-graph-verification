Require Import List.
Import ListNotations.
Require Import Bool.
Require Import Nat.

Require Import Coq.Arith.PeanoNat.

Require Import Coq.Lists.ListSet.
Require Import Coq.Arith.EqNat.

Require Import Coq.Arith.Peano_dec.
Definition eq_nat := eq_nat_dec.

(* Defining an algebraic graph *)

Inductive AG (A : Type) : Type :=
  | Empty
  | Vertex (x : A)
  | Overlay (top bottom : AG A)
  | Connect (left right : AG A).

Arguments Empty {A}.
Arguments Vertex {A}.
Arguments Overlay {A}.
Arguments Connect {A}.

(* Doing the same thing as implementing fromInteger from Haskell *)
Definition from_nat (n:nat) : AG nat :=
    Vertex n.
Coercion from_nat : nat >-> AG.


(* *** has more priority than +++ *)
Notation "ag1 +++ ag2" := (Overlay ag1 ag2) (at level 60, right associativity).
Notation "ag1 *** ag2" := (Connect ag1 ag2) (at level 59, right associativity).



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


Compute countNodes (1 *** 2 +++ 3 *** 4).
Compute countNodes (1 *** 2 +++ 1 *** 2).





(* This a somewhat analogous to DFS *)
(* A little magical, since we are using the returned list as a output list as well as a set *)
Fixpoint searchGraphUnique (ag : AG nat) (s : set nat) : (list nat) :=
    match ag with
    | Empty => []
    | Vertex x => if set_mem eq_nat x s then [] else [x]
    | Overlay ag1 ag2 => match searchGraphUnique ag1 s with
                        | ret => ret ++ searchGraphUnique ag2 (set_union eq_nat s ret)
                        end
    | Connect ag1 ag2 => match searchGraphUnique ag1 s with
                        | ret => ret ++ searchGraphUnique ag2 (set_union eq_nat s ret)
                        end
    end.

(* This is somewhat analogous, but for BFS, but Coq needs more evidence of decreasing argument,
it would need a queue data structure and *)
(* Fixpoint searchGraphUnique' (target : nat) (g : graph nat) : bool :=
  let fix bfs_queue (queue : list (graph nat)) (visited : list nat) : bool :=
    match queue with
    | [] => false
    | Empty :: rest => bfs_queue rest visited
    | Vertex x :: rest =>
        if (x =? target) then true
        else bfs_queue rest (visited ++ [x])
    | Overlay top bottom :: rest => 
        let new_queue := rest ++ [top] ++ [bottom] in
        bfs_queue new_queue visited
    | Connect gleft gright :: rest => 
        let new_queue := rest ++ [gleft] ++ [gright] in
        bfs_queue new_queue visited
    end
  in
  bfs_queue [g] []. *)



Compute searchGraphUnique (1 *** 2 +++ 3 *** 4) [].
Compute searchGraphUnique (1 *** 2 +++ 1 *** 2) [].
Compute searchGraphUnique (1 *** 1) [].
Compute searchGraphUnique (1 +++ 1) [].

Compute searchGraphUnique (1 *** 2 +++ 2 *** 3 +++ 1 *** 3) [].

Definition setEqual (s1 s2 : set nat) : bool.
Proof.
Admitted.

Definition AG_measure {A : Type} (ag : AG A) : nat.
Proof.
Admitted.

Require Import Recdef.

Function recHelper (left right : AG nat) (f : AG nat -> set nat -> set nat) (prev : set nat) {measure AG_measure left} : set nat :=
  let result := f left prev  in if setEqual result prev then recHelper right left f result else result.
Proof.
Admitted.  

 
Fail Function canReachFrom (ag : AG nat) (acc : set nat) {measure AG_measure ag} : set nat :=
  match ag with
    | Empty => acc
    | Vertex x => acc
    | Overlay ag1 ag2 => recHelper ag1 ag2 (fun agx acc => canReachFrom agx acc) acc
    | Connect ag1 ag2 => let ovel := recHelper ag1 ag2 (fun agx acc => canReachFrom agx acc) acc in
                            let RHS := searchGraphUnique ag2 [] in
                            if fold_right (fun x acc => acc || (set_mem eq_nat_dec x RHS)) false acc then acc ++ RHS else acc 
    end.


(* This works in Haskell ;( *)
Fail Function canReachFrom' (ag : AG nat) (acc : set nat) {measure AG_measure ag} : set nat :=
  match ag with
    | Empty => acc
    | Vertex x => acc
    | Overlay ag1 ag2 => let result := canReachFrom' (ag1, acc) in 
                            let result' := canReachFrom' (ag2, result) in 
                            if setEqual acc result' then acc else canReachFrom' (ag, result')

    | Connect ag1 ag2 =>   let result := canReachFrom' (ag1, acc) in 
                            let result' := canReachFrom' (ag2, result) in
                            let LHS := searchGraphUnique ag1 [] in

                            let RHS := searchGraphUnique ag2 [] in
                            let result'' := if existsb (fun x => (set_mem eq_nat_dec x LHS)) result' then result' ++ RHS else result' in
                            if setEqual acc result'' then acc else canReachFrom' (ag, result'')
    end.


Fixpoint listEqual (l1 l2 : list nat) : bool :=
  match l1, l2 with
    | [], [] => true
    | x :: xs, y :: ys => if eq_nat_dec x y then listEqual xs ys else false
    | _, _ => false
  end.

(* Function merge (l1l2 : list nat * list nat) {measure (fun (ll : list nat * list nat) => let (x, y) := ll in length x + length y) l1l2} : list nat :=  
    match l1l2 with
    | ([], l2) => l2
    | (l1, []) => l1
    | (x :: xs, y :: ys) => if (x <? y) then x :: merge (xs, y :: ys) else y :: merge (x :: xs, ys)
    end.
Proof.
Admitted. *)

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






Definition canReachWF (agAcc1 agAcc2 : AG nat * set nat) : Prop.
Proof.
Admitted.


Function canReachFrom' (agAcc : AG nat * set nat) {wf canReachWF agAcc} : set nat :=  
  match agAcc with
    | (ag, acc) => 
  match ag with
    | Empty => acc
    | Vertex x => acc
    | Overlay ag1 ag2 => let result := canReachFrom'(ag1, acc) in 
                            let result' := canReachFrom' (ag2, result) in 
                            if setEqual acc result' then acc else canReachFrom' (ag, result')

    | Connect ag1 ag2 =>   let result := canReachFrom' (ag1, acc) in 
                            let result' := canReachFrom' (ag2, result) in
                            let LHS := searchGraphUnique ag1 [] in

                            let RHS := searchGraphUnique ag2 [] in
                            let result'' := if existsb (fun x => (set_mem eq_nat_dec x LHS)) result' then result' ++ RHS else result' in
                            if setEqual acc result'' then acc else canReachFrom' (ag, result'')
    end
                            end.