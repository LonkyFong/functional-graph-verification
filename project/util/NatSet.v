Require Import FSets.

(* TODO: migrate to Msets *)
Definition Node := Nat_as_OT.t.

Module NatSet := FSetList.Make(Nat_as_OT).
Module NatSetProperties := EqProperties(NatSet).

Definition NatSet_fromList (l : list Node) : NatSet.t :=
    fold_right NatSet.add NatSet.empty l.
