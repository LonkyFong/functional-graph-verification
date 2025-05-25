{-# LANGUAGE DeriveFunctor #-}

import Data.Set (Set)
import qualified Data.Set as Set

-- Graph data type
data AG a = Empty
           | Vertex a
           | Overlay (AG a) (AG a)
           | Connect (AG a) (AG a)
           deriving (Show, Eq, Functor)

-- Utility function to check if two sets are equal
setEqual :: Ord a => Set a -> Set a -> Bool
setEqual = (==)

-- Function to determine if an element exists in a set
setMem :: Ord a => a -> Set a -> Bool
setMem = Set.member

-- searchGraphUnique function (converted from Coq)
searchGraphUnique :: AG Int -> Set Int -> [Int]
searchGraphUnique ag s = case ag of
  Empty -> []
  Vertex x ->
    if setMem x s
      then []
      else [x]
  Overlay ag1 ag2 ->
    let ret = searchGraphUnique ag1 s
        newSet = Set.union s (Set.fromList ret)
    in ret ++ searchGraphUnique ag2 newSet
  Connect ag1 ag2 ->
    let ret = searchGraphUnique ag1 s
        newSet = Set.union s (Set.fromList ret)
    in ret ++ searchGraphUnique ag2 newSet

-- Main canReachFrom' function (as before)
canReachFrom' :: AG Int -> Set Int -> Set Int
canReachFrom' ag acc = case ag of
  Empty -> acc
  Vertex x -> acc
  Overlay ag1 ag2 ->
    let result = canReachFrom' ag1 acc
        result' = canReachFrom' ag2 result
    in if setEqual acc result'
         then acc
         else canReachFrom' ag result'
  Connect ag1 ag2 ->

    let result = canReachFrom' ag1 acc
        result' = canReachFrom' ag2 result
        lhs = Set.fromList (searchGraphUnique ag1 Set.empty)
        rhs = Set.fromList (searchGraphUnique ag2 Set.empty)
        intersection = not $ Set.null $ Set.intersection result' lhs
        result'' = if intersection
                      then Set.union result' rhs
                      else result'
    in if setEqual acc result''
         then acc
         else canReachFrom' ag result''

-- Example usage
main :: IO ()
main = do
  let g = Overlay (Vertex 1) (Connect (Vertex 2) (Vertex 3))
      acc = Set.fromList [1]
  print $ canReachFrom' g acc
  print $ searchGraphUnique g Set.empty
