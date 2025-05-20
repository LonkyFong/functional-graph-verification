Require Import FMaps.


Definition Node := Nat_as_OT.t.

Module NatMap := FMapList.Make(Nat_as_OT).

Module WF := WFacts_fun Nat_as_OT NatMap. (* Library of useful lemmas about maps *)
Module WP := WProperties_fun Nat_as_OT NatMap. (* More useful stuff about maps *)
Print Module WF.
Print Module WP.
Check Nat_as_OT.lt. (*   : positive -> positive -> Prop *)





Module PairNat_as_OT := PairOrderedType(Nat_as_OT)(Nat_as_OT).
Definition NodePair := PairNat_as_OT.t.

Module PairNatMap := FMapList.Make(PairNat_as_OT).

Module PWF := WFacts_fun PairNat_as_OT PairNatMap. (* Library of useful lemmas about maps *)
Module PWP := WProperties_fun PairNat_as_OT PairNatMap. (* More useful stuff about maps *)



Definition filter_map {A : Type} (pred : PairNatMap.key -> A -> bool) (m : PairNatMap.t A) : PairNatMap.t A :=
  PairNatMap.fold (fun k v acc =>
            if pred k v then PairNatMap.add k v acc else acc)
         m
         (PairNatMap.empty A)
.


(* Definition myPairNatMap : PairNatMap.t nat := PairNatMap.empty nat.
Definition myPairNatMap' := PairNatMap.add (1, 2) 3 myPairNatMap.
Compute PairNatMap.find (1, 2) myPairNatMap'.
Definition isIn (keys : nat * nat) (map : PairNatMap.t nat) := PairNatMap.In keys map.
Compute PairNatMap.In (1, 2) myPairNatMap'. *)

