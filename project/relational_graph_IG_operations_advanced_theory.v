Require Import String.
Open Scope string_scope.

Require Import List.
Import ListNotations.

(* Work in progress. So far: copied theorems from fgl paper *)

(*
Require Import Coq.Arith.Arith.

Require Import Bool.


Require Import MyProject.project.util.util.

Require Import MyProject.project.relational_graph_theory.


Require Import Coq.Sets.Ensembles.
Require Import MyProject.project.util.NatSet.
*)

Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Sets.Ensembles.

Require Import MyProject.project.util.util.
Require Import MyProject.project.relational_graph.
Require Import MyProject.project.relational_graph_IG_operations.
Require Import MyProject.project.relational_graph_IG_operations_advanced.





gmap f . gmap f 0 = gmap (f . f 0 )
grev . grev = id

We can prove gmap fusion by induction on the graph structure. For g = Empty we
have by definition gmap f (gmap f 0 Empty) = gmap f Empty = Empty = gmap (f . f 0 )
Empty. Otherwise, with g = c & g 0 we conclude by induction:
gmap f (gmap f 0 g) = gmap f (gmap f 0 (c & g 0 ))
= gmap f (f 0 c & (gmap f 0 g 0 ))
= f (f 0 c) & gmap f (gmap f 0 g 0 )
= (f . f 0 ) c & gmap (f . f 0 ) g 0
= gmap (f . f 0 ) (c & g 0 )
= gmap (f . f 0 ) g


swap . swap = id
gmap id = id



grev . grev = gmap swap . gmap swap
= gmap (swap . swap)
= gmap id
= id