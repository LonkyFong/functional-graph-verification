Require Import MyProject.project.algebraic.algebraic_graph.


(* Associate *** *)
Fixpoint Setp_O {A : Type} (ag : AG A) : AG A :=
  match ag with
  | Empty => Empty
  | Vertex x => Vertex x
  | (ag1 *** ag2) *** ag3 => Setp_O ag1 *** (Setp_O ag2 *** Setp_O ag3)
  | ag1 +++ ag2 => Setp_O ag1 +++ Setp_O ag2
  | ag1 *** ag2 => Setp_O ag1 *** Setp_O ag2
  end.

(* Distribute *** over +++ *)
Fixpoint Setp_1 {A : Type} (ag : AG A) : AG A :=
  match ag with
  | Empty => Empty
  | Vertex x => Vertex x
  | ag1 *** (ag2 +++ ag3) => (Setp_1 ag1 *** Setp_1 ag2) +++ (Setp_1 ag1 *** Setp_1 ag3)
  | (ag1 +++ ag2) *** ag3 => (Setp_1 ag1 *** Setp_1 ag3) +++ (Setp_1 ag2 *** Setp_1 ag3)
  | ag1 +++ ag2 => Setp_1 ag1 +++ Setp_1 ag2
  | ag1 *** ag2 => Setp_1 ag1 *** Setp_1 ag2
  end.


(* Decompose *** *** *)
Fixpoint Setp_2 {A : Type} (ag : AG A) : AG A :=
  match ag with
  | Empty => Empty
  | Vertex x => Vertex x
  | ag1 *** (ag2 *** ag3) => Setp_2 ag1 *** Setp_2 ag2 +++ (Setp_2 ag1 *** Setp_2 ag3 +++ Setp_2 ag2 *** Setp_2 ag3)
  | ag1 +++ ag2 => Setp_2 ag1 +++ Setp_2 ag2
  | ag1 *** ag2 => Setp_2 ag1 *** Setp_2 ag2
  end.




(* Associate +++ *)
Fixpoint Setp_3 {A : Type} (ag : AG A) : AG A :=
  match ag with
  | Empty => Empty
  | Vertex x => Vertex x
  (* Here, Setp_3 should probably be called on the whole expression once more (in similar other places probably too), but fixpoint does not allow it *)
  | (ag1 +++ ag2) +++ ag3 => Setp_3 ag1 +++ (Setp_3 ag2 +++ Setp_3 ag3)
  | ag1 +++ ag2 => Setp_3 ag1 +++ Setp_3 ag2
  | ag1 *** ag2 => Setp_3 ag1 *** Setp_3 ag2
  end.

Definition All_Setp {A : Type} (ag : AG A) : AG A :=
    Setp_3
     (Setp_2 (Setp_1
    (Setp_O ag)
    )
    )
.

Compute All_Setp (1 *** 2 +++ 3 *** 4).
Compute All_Setp (1 *** (2 *** 3)).
(* big, compilicated example *)
Compute All_Setp (1 *** (2 +++ 3) +++ 4 *** (5 +++ (6 *** 7)) +++ 8).
(* here, the simplification breaks *)
Compute All_Setp (1 *** 2 +++ ((4 *** 6 *** 7)) +++ 8). 

Compute All_Setp (((((2 +++ 4) +++ 6) +++ 3))).
Compute All_Setp (1 +++ 2 +++ 3 +++ 4).




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