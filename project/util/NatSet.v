Require Import FSets.

Definition Node := Nat_as_OT.t.

Module NatSet := FSetList.Make(Nat_as_OT).
Module NatSetProperties := EqProperties(NatSet).
