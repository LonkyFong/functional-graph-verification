(* Defining an algebraic graph *)
Inductive AG (A : Type) : Type :=
  | Empty
  | Vertex (x : A)
  | Overlay (top bottom : AG A)
  | Connect (left right : AG A).

Arguments Empty {A}.
Arguments Vertex {A}.
Arguments Overlay {A}.
Arguments Connect {A}.

(* Doing the same thing as implementing fromInteger from Haskell *)
Definition from_nat (n:nat) : AG nat :=
    Vertex n.
Coercion from_nat : nat >-> AG.


(* *** has more priority than +++ *)
Notation "g1 +++ g2" := (Overlay g1 g2) (at level 60, right associativity).
Notation "g1 *** g2" := (Connect g1 g2) (at level 59, right associativity).


