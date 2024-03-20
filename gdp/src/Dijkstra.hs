{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module Dijkstra (Graph (..), Distance (..), dijkstra, classifyDistancePositiveGraph, classifyGraph, classifyNodeInGraph) where

import Data.Refined ((...), type (:::))
import Data.The
import Logic.Proof (Proof, axiom)
import Logic.Propositional (introAnd, type (/\))
import MinHeap as H
  ( MinHeap,
    classifyHeapNotEmpty,
    extractMin,
    fromList,
    insert,
    isEmpty,
    isValidMinHeap,
  )
import Theory.Named (name, name2, type (~~))

-- | A HashMap is a list of key-value pairs.
type HashMap k v = [(k, v)]

-- | A HashSet is a list of elements.
type HashSet a = [a]

-- | distance is either a number or infinity.
data Distance a = Dist a | Infinity
  deriving (Show, Eq)

instance (Ord a) => Ord (Distance a) where
  Infinity <= Infinity = True
  Infinity <= Dist _ = False
  Dist _ <= Infinity = True
  Dist x <= Dist y = x <= y

-- | Add two distances together, returning Infinity if either is Infinity.
addDist :: (Num a) => Distance a -> Distance a -> Distance a
addDist (Dist x) (Dist y) = Dist (x + y)
addDist _ _ = Infinity

-- | Get the neighbors of a node in a graph.
-- Preconditions:
-- 1. The node is in the graph
-- 2. The graph is valid
neighbors :: (String ~~ s1 ::: NodeInGraph s1 g) -> (Graph ~~ g ::: IsValidGraph g) -> [(String, Int)]
neighbors (The node) (The g) = case lookup node (edges g) of
  Just x -> x
  Nothing -> []

-- | Get the value of a key in a map, or Infinity if the key is not present.
(!??) :: (Eq k) => HashMap k (Distance d) -> k -> Distance d
(!??) m key = case (lookup key m) of
  Just x -> x
  Nothing -> Infinity

-- | A graph is a map from nodes to their neighbors.
newtype Graph = Graph
  {edges :: HashMap String [(String, Int)]}

-- | The state of Dijkstra's algorithm.
data DijkstraState n = DijkstraState
  { visitedSet :: HashSet String,
    distanceMap :: HashMap String (Distance Int),
    nodeQueue :: MinHeap (Distance Int) String
  }
  deriving (Show)

-- | Initialize the state of Dijkstra's algorithm.
-- Preconditions:
-- 1. The start node is in the graph
-- 2. The graph is valid
-- 3. The graph has positive distances
initialState :: (String ~~ s1 ::: NodeInGraph s1 g) -> (Graph ~~ g ::: IsValidGraph g /\ DistancePositiveGraph g) -> (forall n. (Graph ~~ g ::: IsValidGraph g /\ DistancePositiveGraph g) -> DijkstraState n -> r) -> r
initialState (The start) g f = case H.fromList [(Dist 0, start)] of
  Just q -> f g $ DijkstraState [] [(start, Dist 0)] $ q
  Nothing -> error "intialState: invalid initial heap"

-- | Run Dijkstra's algorithm on a graph, starting from a given node.
-- The result is a map of distances from the start node to all other nodes.
-- Preconditions:
-- 1. The start node is in the graph
-- 2. The end node is in the graph
-- 3. The graph is valid
-- 4. The graph has positive distances
dijkstra :: (String ~~ s1 ::: NodeInGraph s1 g) -> (String ~~ s2 ::: NodeInGraph s2 g) -> (Graph ~~ g ::: IsValidGraph g /\ DistancePositiveGraph g) -> Distance Int
dijkstra start (The end) graph = (initialState start graph $ \g s -> go g s) !?? end
  where
    go :: (Graph ~~ g ::: IsValidGraph g /\ DistancePositiveGraph g) -> DijkstraState n -> HashMap String (Distance Int)
    go g s
      | H.isEmpty (nodeQueue s) = distanceMap s
      | otherwise = go g $ step g s

-- | Perform one step of Dijkstra's algorithm.
-- Preconditions:
-- 1. The graph is valid
-- 2. The graph has positive distances
step :: (Graph ~~ g ::: IsValidGraph g /\ DistancePositiveGraph g) -> DijkstraState n -> DijkstraState n
step (The g) s = name (nodeQueue s) $ \mh -> case do
  -- setup proof of non-empty heap and valid minheap
  (sizeProof) <- H.classifyHeapNotEmpty mh
  (validProof) <- H.isValidMinHeap mh
  let (((d, node)), q) = H.extractMin (mh ... (sizeProof `introAnd` validProof))

  case d of
    Infinity -> Nothing
    Dist _ -> name2 node g $ \n g' -> do
      -- setup proof of node in graph and valid graph
      (nodeProof) <- classifyNodeInGraph n g'
      (graphProof) <- classifyGraph g'

      -- update state
      Just $ foldr (checkNeighbor node) (DijkstraState (node : visitedSet s) (distanceMap s) q) (neighbors (n ... nodeProof) (g' ... graphProof)) of
  Nothing -> s
  Just s' -> s'

-- | Update the state based on a neighbor of the current node.
checkNeighbor :: String -> (String, Int) -> DijkstraState n -> DijkstraState n
checkNeighbor node (neighbor, weight) s
  | neighbor `elem` visitedSet s = s
  | newDist < (distanceMap s !?? neighbor) = name (nodeQueue s) $ \nq -> case do
      proof <- H.isValidMinHeap nq
      let rq = H.insert (newDist, neighbor) (nq ... proof)
      return $ DijkstraState (visitedSet s) ((neighbor, newDist) : distanceMap s) rq of
      Just s' -> s'
      Nothing -> s
  | otherwise = s
  where
    newDist = addDist (Dist weight) (distanceMap s !?? node)

--- GDP Stuff

data IsValidGraph g

data NodeInGraph s g

data DistancePositiveGraph g

-- | Classify the graph as valid.
classifyGraph :: (Graph ~~ g) -> Maybe (Proof (IsValidGraph g))
classifyGraph (The (Graph g)) = case all (all ((`elem` map fst g) . fst) . snd) g of
  True -> Just axiom
  False -> Nothing

-- | Classify the node as being in the graph.
classifyNodeInGraph :: (String ~~ s) -> (Graph ~~ g) -> Maybe (Proof (NodeInGraph s g))
classifyNodeInGraph (The s) (The (Graph g)) = case s `elem` (map fst g) of
  True -> Just axiom
  False -> Nothing

-- | Classify the distance as being positive in the graph.
classifyDistancePositiveGraph :: (Graph ~~ g) -> Maybe (Proof (DistancePositiveGraph g))
classifyDistancePositiveGraph (The (Graph g)) = case all (all ((>= 0) . snd) . snd) g of
  True -> Just axiom
  False -> Nothing

