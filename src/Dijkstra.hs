module Dijkstra where

-- https://mmhaskell.com/blog/2022/8/22/dijkstras-algorithm-in-haskell

import Data.HashSet (HashSet)
import Data.Hashable (Hashable)
import MinHeap

data Distance a = Dist a | Infinity
  deriving (Show, Eq)

instance (Ord a) => Ord (Distance a) where
  Infinity <= Infinity = True
  Infinity <= Dist _ = False
  Dist _ <= Infinity = True
  Dist x <= Dist y = x <= y

addDist :: (Num a) => Distance a -> Distance a -> Distance a
addDist (Dist x) (Dist y) = Dist (x + y)
addDist _ _ = Infinity

-- (!??) :: (HM.Hashable k, Eq k) => HM.HashMap k (Distance d) -> k -> Distance d
-- (!??) distanceMap key = fromMaybe Infinity (HM.lookup key distanceMap)

-- newtype Graph = Graph
--   {edges :: HM.HashMap String [(String, Int)]}