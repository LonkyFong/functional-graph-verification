Require Import MyProject.project.algebraic.algebraic_graph.

Require Import Recdef.

(* This hit a wall, since rewriting to make the expression smaller again is a difficult task *)

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



(* Associate +++ *)
Function associateOverlay {A : Type} (ag : AG A) {measure AG_measure ag} : AG A :=
  match ag with
  | Empty => Empty
  | Vertex x => Vertex x
  | (ag1 +++ ag2) +++ ag3 => associateOverlay (ag1 +++ (ag2 +++ ag3))
  | ag1 +++ ag2 => associateOverlay ag1 +++ associateOverlay ag2
  | ag1 *** ag2 => associateOverlay ag1 *** associateOverlay ag2
  end.
Proof.
Admitted.


Fixpoint eliminateEmpties {A : Type} (ag : AG A) : AG A :=
  match ag with
  | Empty => Empty
  | Vertex x => Vertex x
  | Empty +++ ag1 => eliminateEmpties ag1
  | ag1 +++ Empty => eliminateEmpties ag1
  | Empty *** ag1 => eliminateEmpties ag1
  | ag1 *** Empty => eliminateEmpties ag1
  | ag1 +++ ag2 => eliminateEmpties ag1 +++ eliminateEmpties ag2
  | ag1 *** ag2 => eliminateEmpties ag1 *** eliminateEmpties ag2
  end.




Definition AG_CNF {A : Type} (ag : AG A) : AG A :=
  eliminateEmpties
    (associateOverlay A
    (decomposeConnect A
    (distributeConnectOverlay A
    (associateConnect A
    ag)
    )
    )
    )
  .



Ltac AG_simplify_fake_compute := 
repeat (rewrite associateConnect_equation; simpl);
repeat (rewrite distributeConnectOverlay_equation; simpl);
repeat (rewrite decomposeConnect_equation; simpl);
repeat (rewrite associateOverlay_equation; simpl).

Compute AG_CNF (1 *** 2 +++ 3 *** 4).

Example AG_CNF_test : exists n, AG_CNF (1 *** 2 +++ 3 *** 4) = n.
Proof.
  unfold AG_CNF.
  AG_simplify_fake_compute.
  exists (Vertex 1 *** Vertex 2 +++ Vertex 3 *** Vertex 4).
  reflexivity.
Qed.

Compute AG_CNF (1 *** (2 *** 3)).

Example AG_CNF_test' : exists n, AG_CNF (1 *** (2 *** 3)) = n.
Proof.
  unfold AG_CNF.
  AG_simplify_fake_compute.
  exists (Vertex 1 *** Vertex 2 +++ Vertex 1 *** Vertex 3 +++ Vertex 2 *** Vertex 3).
  reflexivity.
Qed.

(* big, compilicated example *)
Compute AG_CNF (1 *** (2 +++ 3) +++ 4 *** (5 +++ (6 *** 7)) +++ 8).
Example AG_CNF_test''' : exists n, AG_CNF (1 *** 2 +++ ((4 *** 6 *** 7)) +++ 8) = n.
Proof.
  unfold AG_CNF.
  AG_simplify_fake_compute.
  exists (Vertex 1 *** Vertex 2 +++ Vertex 4 *** Vertex 6 +++ Vertex 4 *** Vertex 7 +++ Vertex 6 *** Vertex 7 +++ Vertex 8).
  reflexivity.
Qed.



(* here, the simplification breaks *)
Compute AG_CNF (1 *** 2 +++ ((4 *** 6 *** 7)) +++ 8). 

Example AG_CNF_test'''' : exists n, AG_CNF (1 *** 2 +++ ((4 *** 6 *** 7)) +++ 8) = n.
Proof.
  unfold AG_CNF.
  AG_simplify_fake_compute.
  exists (Vertex 1 *** Vertex 2 +++ Vertex 4 *** Vertex 6 +++ Vertex 4 *** Vertex 7 +++ Vertex 6 *** Vertex 7 +++ Vertex 8).
  reflexivity.
Qed.

Compute AG_CNF (((((2 +++ 4) +++ 6) +++ 3))).

Example AG_CNF_test''''' : exists n, AG_CNF (((((2 +++ 4) +++ 6) +++ 3))) = n.
Proof.
  unfold AG_CNF.
  AG_simplify_fake_compute.
  exists ( Vertex 2 +++ Vertex 4 +++ Vertex 6 +++ Vertex 3).
  reflexivity.
Qed.

Compute AG_CNF (1 +++ 2 +++ 3 +++ 4).

Example AG_CNF_test'''''' : exists n, AG_CNF (1 +++ 2 +++ 3 +++ 4) = n.
Proof.
  unfold AG_CNF.
  AG_simplify_fake_compute.
  exists (Vertex 1 +++ Vertex 2 +++ Vertex 3 +++ Vertex 4).
  reflexivity.
Qed.

Require Import List.
Import ListNotations.

Compute clique [1; 2; 3].

Lemma always_exists : forall (A : Type) (s : A), exists n : A, s = n.
Proof.
  intros. exists s. reflexivity.
Qed.


Example AG_CNF_test''''''' : exists n, AG_CNF (Vertex 1 *** Vertex 2 *** Vertex 3 *** Vertex 4 *** Vertex 5 *** Empty) = n.
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



(* Now, the expression is O(edges + nodes). Which is possibly exponential in the original expression's size, since distributivity can cause things to blow up *)


(* -- TODO: Find a more efficient equality check. Note that assuming the Strong
-- Exponential Time Hypothesis (SETH), it is impossible to compare two algebraic
-- graphs in O(s^1.99), i.e. a quadratic algorithm is the best one can hope for.

-- Check if two graphs are equal by converting them to their adjacency maps.
eqR :: Ord a => Graph a -> Graph a -> Bool
eqR x y = toAdjacencyMap x == toAdjacencyMap y *)


(* -- TODO: This is a very inefficient implementation. Find a way to construct an
-- adjacency map directly, without building intermediate representations for all
-- subgraphs.
-- Convert a graph to 'AM.AdjacencyMap'.
toAdjacencyMap :: Ord a => Graph a -> AM.AdjacencyMap a
toAdjacencyMap = foldg AM.empty AM.vertex AM.overlay AM.connect *)


(* simplify :: Ord a => Graph a -> Graph a
simplify = foldg Empty Vertex (simple Overlay) (simple Connect)
{-# INLINE simplify #-}
{-# SPECIALISE simplify :: Graph Int -> Graph Int #-}

simple :: Eq g => (g -> g -> g) -> g -> g -> g
simple op x y
    | x == z    = x
    | y == z    = y
    | otherwise = z
  where
    z = op x y *)






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