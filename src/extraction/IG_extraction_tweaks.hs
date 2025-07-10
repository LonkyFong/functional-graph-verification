-- Tweaks to make the extracted inductive graphs code more usable
-- These are just code snippets, not complete executable Haskell code.

-- In preamble
module IG_extracted_tweaked where


-- make each of these datatypes derive Show, such that results can be displayed
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