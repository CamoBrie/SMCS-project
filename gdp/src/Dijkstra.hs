{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module Dijkstra where

-- https://mmhaskell.com/blog/2022/8/22/dijkstras-algorithm-in-haskell

import Debug.Trace (traceShow)
import MinHeap as H

type HashMap k v = [(k, v)]

type HashSet a = [a]

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

neighbors :: String -> Graph -> [(String, Int)]
neighbors node g = case lookup node (edges g) of
  Just x -> x
  Nothing -> []

(!??) :: (Eq k) => HashMap k (Distance d) -> k -> Distance d
(!??) m key = case (lookup key m) of
  Just x -> x
  Nothing -> Infinity

newtype Graph = Graph
  {edges :: HashMap String [(String, Int)]}

data DijkstraState n = DijkstraState
  { visitedSet :: HashSet String,
    distanceMap :: HashMap String (Distance Int),
    nodeQueue :: H.Sized n (MinHeap (Distance Int) String)
  }
  deriving (Show)

-- | Run Dijkstra's algorithm on a graph, starting from a given node.
initialState :: String -> Graph -> (forall n. Graph -> DijkstraState n -> r) -> r
initialState start g f = H.fromList [(Dist 0, start)] $ \h -> f g $ DijkstraState [] [(start, Dist 0)] h

-- | Run Dijkstra's algorithm on a graph, starting from a given node.
-- The result is a map of distances from the start node to all other nodes.
dijkstra :: String -> String -> Graph -> Distance Int
dijkstra start end graph = (initialState start graph $ \g s -> go g s) !?? end
  where
    go :: Graph -> DijkstraState n -> HashMap String (Distance Int)
    go g s
      | H.isEmpty (nodeQueue s) = distanceMap s
      | otherwise = go g $ step g s

-- | Perform one step of Dijkstra's algorithm.
step :: Graph -> DijkstraState n -> DijkstraState n
step g s = traceShow s $ case H.extractMin (nodeQueue s) of
  Just ((Infinity, _), _) -> s
  Just ((Dist _, node), q) -> foldr (checkNeighbor node) (DijkstraState (node : visitedSet s) (distanceMap s) q) (neighbors node g)
  Nothing -> s

-- | Update the state based on a neighbor of the current node.
checkNeighbor :: String -> (String, Int) -> DijkstraState n -> DijkstraState n
checkNeighbor node (neighbor, weight) s
  | neighbor `elem` visitedSet s = s
  | otherwise =
      let newDist = addDist (Dist weight) (distanceMap s !?? node)
       in case newDist < (distanceMap s !?? neighbor) of
            True -> DijkstraState (visitedSet s) ((neighbor, newDist) : distanceMap s) (H.insert (newDist, neighbor) (nodeQueue s))
            False -> s

-- example graph
exampleGraph :: Graph
exampleGraph =
  Graph
    [ ("A", [("D", 100), ("B", 1), ("C", 20)]),
      ("B", [("D", 50)]),
      ("C", [("D", 20)]),
      ("D", [])
    ]
