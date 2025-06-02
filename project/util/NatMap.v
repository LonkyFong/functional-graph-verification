Require Import FMaps.
Require Export FMapAVL.

(* Instantiate an FMap module, such that it is the same across the whole project *)

Definition Node := Nat_as_OT.t.

Print Module FMaps.

(* Uses the quick AVL-tree variant *)
Module NatMap := FMapAVL.Make(Nat_as_OT).

(* Library of useful lemmas about maps *)
Module MFacts := WFacts_fun Nat_as_OT NatMap.
(* More useful lemmas about maps *)
Module MProps := WProperties_fun Nat_as_OT NatMap.
