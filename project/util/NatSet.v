Require Import MSets.

(* Instantiate an FSet module, such that it is the same across the whole project *)


Definition Node := Nat_as_OT.t.

(* Uses the quick AVL-tree variant *)
Module NatSet := MSetAVL.Make(Nat_as_OT).
Module SProps := EqProperties(NatSet).

(* Custom additional function for NatSets "fromList" *)
Definition NatSet_fromList (l : list Node) : NatSet.t :=
    fold_right NatSet.add NatSet.empty l.
