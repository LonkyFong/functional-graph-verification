-- Tweaks to make the extracted algebraic graphs code more usable.
-- These are just code snippets, not complete executable Haskell code.

-- In Preamble
module AG_extracted_tweaked where

import qualified Prelude
import Prelude ((+), (*), fromInteger, signum, abs, negate)



-- Enhanced defintion of AGs
data AG a =
   AG_empty
 | AG_vertex a
 | AG_overlay (AG a) (AG a)
 | AG_connect (AG a) (AG a)
     deriving (Prelude.Show)
    

instance (Prelude.Ord a, Prelude.Num a) => Prelude.Num (AG a) where
    fromInteger = AG_vertex Prelude.. fromInteger
    (+) = AG_overlay
    (*) = AG_connect
    signum = Prelude.const AG_empty
    abs = Prelude.id
    negate = Prelude.id