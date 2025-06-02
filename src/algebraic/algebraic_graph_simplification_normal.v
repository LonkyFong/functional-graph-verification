Require Import MyProject.src.algebraic.algebraic_graph.

Require Import Recdef.


(* This hit a wall, since rewriting to make the expression smaller again is a difficult task *)
(* This file tries to go via some intermediate representation, but does not succeed *)

Definition AG_measure {A : Type} (ag : AG A) : nat.
Proof.
Admitted.

(* Associate *** *)
Function associateConnect {A : Type} (ag : AG A) {measure AG_measure ag} : AG A :=
  match ag with
  | Empty => Empty
  | Vertex x => Vertex x
  | (ag1 *** ag2) *** ag3 => associateConnect (ag1 *** (ag2 *** ag3))
  | ag1 +++ ag2 => associateConnect ag1 +++ associateConnect ag2
  | ag1 *** ag2 => associateConnect ag1 *** associateConnect ag2
  end.
Proof.
Admitted.

(* Distribute *** over +++ *)
Function distributeConnectOverlay {A : Type} (ag : AG A) {measure AG_measure ag} : AG A :=
  match ag with
  | Empty => Empty
  | Vertex x => Vertex x
  | ag1 *** (ag2 +++ ag3) => distributeConnectOverlay ((ag1 *** ag2) +++ (ag1 *** ag3))
  | (ag1 +++ ag2) *** ag3 => distributeConnectOverlay ((ag1 *** ag3) +++ (ag2 *** ag3))
  | ag1 +++ ag2 => distributeConnectOverlay ag1 +++ distributeConnectOverlay ag2
  | ag1 *** ag2 => distributeConnectOverlay ag1 *** distributeConnectOverlay ag2
  end.
Proof.
Admitted.


(* Decompose *** *** *)
Function decomposeConnect {A : Type} (ag : AG A) {measure AG_measure ag} : AG A :=
  match ag with
  | Empty => Empty
  | Vertex x => Vertex x
  | ag1 *** (ag2 *** ag3) => decomposeConnect (ag1 *** ag2 +++ (ag1 *** ag3 +++ ag2 *** ag3))
  | ag1 +++ ag2 => decomposeConnect ag1 +++ decomposeConnect ag2
  | ag1 *** ag2 => decomposeConnect ag1 *** decomposeConnect ag2
  end.
Proof.
Admitted.



Require Import List.
Import ListNotations.

(* A normalized algebraic graph, is just a collection of edges and SINGLETON nodes *)
Definition AG_n (A : Type) : Type :=
  (list A * list (A * A)).

Definition AG_n_Empty {A : Type} : AG_n A :=
  ([], []).

Definition AG_n_insSingleton {A : Type} (x : A) (agn : AG_n A) : AG_n A :=
  match agn with
  | (froms, tos) => (x :: froms, tos)
  end.

Definition AG_n_insEdge {A : Type} (edge : A * A) (agn : AG_n A) : AG_n A :=
  match agn with
  | (froms, tos) => (froms, edge :: tos)
  end.

Definition AG_n_merge {A : Type} (agn1 agn2 : AG_n A) : AG_n A :=
  match agn1, agn2 with
  | (froms1, tos1), (froms2, tos2) => (froms1 ++ froms2, tos1 ++ tos2)
  end.
  


(* Associate +++ *)
Function associateOverlay {A : Type} (ag : AG A) {measure AG_measure ag} : AG_n A :=
  match ag with
  | Empty => AG_n_Empty
  | Vertex x => AG_n_insSingleton x AG_n_Empty
  | Vertex x1 *** Vertex x2 => AG_n_insEdge (x1, x2) AG_n_Empty
  | (ag1 +++ ag2) +++ ag3 => associateOverlay (ag1 +++ (ag2 +++ ag3))
  | ag1 +++ ag2 => AG_n_merge (associateOverlay ag1) (associateOverlay ag2)
  (* This case should never happen, since the input is expected to be in some CNF *)
  | ag1 *** ag2 => AG_n_merge (associateOverlay ag1) (associateOverlay ag2)
  end.
Proof.
Admitted.

Require Import List.
Import ListNotations.
Require Import Bool.
Require Import Nat.

Require Import Coq.Arith.PeanoNat.

Require Import Coq.Lists.ListSet.
Require Import Coq.Arith.EqNat.

Require Import Coq.Arith.Peano_dec.


Compute 1 =? 2.

Locate "=?".

Check Nat.eqb.








Definition eliminateDuplicates (agn : AG_n nat) : AG_n nat := 
  match agn with
  | (singletons, edges) => (
    fold_right (fun x acc => if existsb (eqb x) acc then acc else x :: acc) [] singletons,
  
    fold_right (fun '((x1, x2) : nat * nat) acc => if existsb (fun '((n1, n2) : nat * nat) => (x1 =? n1) &&  Nat.eqb  x2 n2) acc then acc else (x1, x2) :: acc) [] edges
    )  
  end.




Definition eliminateRedundantSingletons (agn : AG_n nat) : AG_n nat := 
  match agn with
  | (singletons, edges) => (
    filter (fun x => negb (existsb (fun '(n1, n2) => (x =? n1) || (x =? n2)) edges)) singletons, 
    edges
  )
  end.





Definition AG_CNF (ag : AG nat) : AG_n nat := 
  eliminateRedundantSingletons
    (eliminateDuplicates
    (associateOverlay nat
    (decomposeConnect nat
    (distributeConnectOverlay nat
    (associateConnect nat
    ag)
    )
    )
    )
    )
  .





Ltac AG_simplify_fake_compute := 
repeat (rewrite associateConnect_equation; simpl);
repeat (rewrite distributeConnectOverlay_equation; simpl);
repeat (rewrite decomposeConnect_equation; simpl);
repeat (rewrite associateOverlay_equation; simpl).

Lemma always_exists : forall (A : Type) (s : A), exists n : A, s = n.
Proof.
  intros. exists s. reflexivity.
Qed.

Compute AG_CNF (1 *** 2 +++ 3 *** 4).

Example AG_CNF_test : exists n, AG_CNF (1 *** 2 +++ 3 *** 4) = n.
Proof.
  unfold AG_CNF.
  AG_simplify_fake_compute.
  apply always_exists.
Qed.

Compute AG_CNF (1 *** (2 *** 3)).

Example AG_CNF_test' : exists n, AG_CNF (1 *** (2 *** 3)) = n.
Proof.
  unfold AG_CNF.
  AG_simplify_fake_compute.
  apply always_exists.
Qed.

(* big, compilicated example *)
Compute AG_CNF (1 *** (2 +++ 3) +++ 4 *** (5 +++ (6 *** 7)) +++ 8).
Example AG_CNF_test''' : exists n, AG_CNF (1 *** (2 +++ 3) +++ 4 *** (5 +++ (6 *** 7)) +++ 8) = n.
Proof.
  unfold AG_CNF.
  AG_simplify_fake_compute.
  apply always_exists.
Qed.



(* here, the simplification breaks *)
Compute AG_CNF (1 *** 2 +++ ((4 *** 6 *** 7)) +++ 8). 

Example AG_CNF_test'''' : exists n, AG_CNF (1 *** 2 +++ ((4 *** 6 *** 7)) +++ 8) = n.
Proof.
  unfold AG_CNF.
  AG_simplify_fake_compute.
  apply always_exists.

Qed.

Compute AG_CNF (((((2 +++ 4) +++ 6) +++ 3))).

Example AG_CNF_test''''' : exists n, AG_CNF (((((2 +++ 4) +++ 6) +++ 3))) = n.
Proof.
  unfold AG_CNF.
  AG_simplify_fake_compute.
  apply always_exists.

Qed.

Compute AG_CNF (1 +++ 2 +++ 3 +++ 4).

Example AG_CNF_test'''''' : exists n, AG_CNF (1 +++ 2 +++ 3 +++ 4) = n.
Proof.
  unfold AG_CNF.
  AG_simplify_fake_compute.
  apply always_exists.

Qed.

Require Import List.
Import ListNotations.

Compute clique [1; 2; 3].




Example AG_CNF_test''''''' : exists n, AG_CNF (Vertex 1 *** Vertex 2 *** Vertex 3 *** Vertex 4 ***  Empty) = n.
Proof.
  unfold AG_CNF.
  AG_simplify_fake_compute.
  apply always_exists.
Qed.

Example K_Map_helper : exists n, AG_CNF (1 *** (2 +++ 3)) = n.
Proof.
  unfold AG_CNF.
  AG_simplify_fake_compute.
  apply always_exists.
Qed.


(* TODO: Now, I will try to apply the rewrite rules to an AG *)

(* a) A -> B + B -> C + A -> C => A -> B -> C *)
(* b) A -> B + A -> C => A -> (B + C) *)
(* c) A -> B + C -> B => (A + C) -> B *)

(* Problem: A -> B + B -> C + A -> C + A -> D + B -> D + C -> D => A -> B -> C + A -> D + B -> D + C -> D no way to continue!! *)

(* Problem: A -> B + A -> C + B -> D + C -> D => A -> B -> D + A -> C -> D (suboptimal!!!)
or => A -> (B + C) -> D (optimal, but b) before a) ..)
*)

(* In case b) before a):
A -> B + B -> C + A -> C => A (B + C) + B -> C (suboptimal!!)
*)

(* The takeaway is, it is not easy to predict, which rule should be used. instead, one could try both and have an exponential explosion of possible rewrite options *)







(* Conversion to relational representation, for euality checking: *)

(* Fixpoint toSet' (ag : AG nat) : fSetAVLNatGraph :=
    match g with
    | Empty => empty_graphAVL
    | Vertex x => insNodeAVL empty_graphAVL x
    | Overlay ag1 ag2 => unionGraphsAVL (toSet' g1) (toSet' g2)
    | Connect ag1 ag2 =>
        match (toSet' g1, toSet' g2) with
        | ((from_nodes, from_edges) as g1', (to_nodes, to_edges) as g2')
            => insEdgesAVL (unionGraphsAVL g1' g2') (setProdAVL from_nodes to_nodes)
        end
    end.

Check fold_right.

Definition fromSet' (g : fSetAVLNatGraph) : graph nat :=
    match g with
    | (nodes, edges) => fold_right Overlay Empty (map (fun x => Vertex x) (NS.elements nodes)) +++ 
                        fold_right Overlay Empty (map (fun x => Connect (Vertex (fst x)) (Vertex (snd x))) (PS.elements edges))
    end.



Definition buildCanonicalForm'' (ag :graph nat) : graph nat :=
    fromSet (toSet g).



Compute buildCanonicalForm'' (1 *** 2 +++ 3 *** 4).
Compute buildCanonicalForm'' (1 *** (2 +++ 3)).

Compute elementsAVL (toSet' (1 *** 2 +++ 3 *** 4)). *)