(* Defining an algebraic graph *)
Inductive AG (X : Type) : Type :=
  | Empty
  | Vertex (x : X)
  | Overlay (top bottom : AG X)
  | Connect (left right : AG X).

Arguments Empty {X}.
Arguments Vertex {X}.
Arguments Overlay {X}.
Arguments Connect {X}.

(* Doing the same thing as implementing fromInteger from Haskell *)
Definition from_nat (n:nat) : AG nat :=
    Vertex n.
Coercion from_nat : nat >-> AG.


(* *** has more priority than +++ *)
Notation "g1 +++ g2" := (Overlay g1 g2) (at level 60, right associativity).
Notation "g1 *** g2" := (Connect g1 g2) (at level 59, right associativity).




