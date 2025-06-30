data Option a =
    Some a
    | None
        deriving (Prelude.Show)


data Positive =
    XI Positive
    | XO Positive
    | XH
        deriving (Prelude.Show)


data Z =
    Z0
    | Zpos Positive
    | Zneg Positive
        deriving (Prelude.Show)


data Tree elt =
    Leaf
    | Node0 (Tree elt) Key elt (Tree elt) T0
        deriving (Prelude.Show)