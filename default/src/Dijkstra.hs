module Dijkstra where

-- https://mmhaskell.com/blog/2022/8/22/dijkstras-algorithm-in-haskell

import Data.Maybe (fromMaybe)
import MinHeap as H (MinHeap, extractMin, fromList, insert)

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

(!??) :: (Eq k) => HashMap k (Distance d) -> k -> Distance d
(!??) m key = fromMaybe Infinity (lookup key m)

newtype Graph = Graph
  {edges :: HashMap String [(String, Int)]}

data DijkstraState = DijkstraState
  { visitedSet :: HashSet String,
    distanceMap :: HashMap String (Distance Int),
    nodeQueue :: MinHeap (Distance Int) String
  }
  deriving (Show)

findShortestDistance :: Graph -> String -> String -> Distance Int
findShortestDistance graph src dest = processQueue initialState !?? dest
  where
    initialVisited = []
    initialDistances = [(src, (Dist 0))]
    initialQueue = H.fromList [(Dist 0, src)]
    initialState = DijkstraState initialVisited initialDistances initialQueue

    processQueue :: DijkstraState -> HashMap String (Distance Int)
    processQueue ds@(DijkstraState v0 d0 q0) = case H.extractMin q0 of
      Nothing -> d0
      Just ((_, node), q1) ->
        if node == dest
          then d0
          else
            if node `elem` v0
              then processQueue (ds {nodeQueue = q1})
              else -- Update the visited set

                let v1 = node : v0
                    -- Get all unvisited neighbors of our current node
                    allNeighbors = fromMaybe [] (lookup node (edges graph))
                    unvisitedNeighbors = filter (\(n, _) -> not (n `elem` v1)) allNeighbors
                 in -- Fold each neighbor and recursively process the queue
                    processQueue $ foldl (foldNeighbor node) (DijkstraState v1 d0 q1) unvisitedNeighbors

    foldNeighbor :: String -> DijkstraState -> (String, Int) -> DijkstraState
    foldNeighbor current ds@(DijkstraState v1 d0 q1) (neighborNode, cost) =
      let altDistance = addDist (d0 !?? current) (Dist cost)
       in if altDistance < d0 !?? neighborNode
            then DijkstraState v1 ((neighborNode, altDistance) : d0) (H.insert (altDistance, neighborNode) q1)
            else ds

-- Example graph
graph1 :: Graph
graph1 =
  Graph $
    [ ("A", [("D", 100), ("B", 1), ("C", 20)]),
      ("B", [("D", 50)]),
      ("C", [("D", 20)]),
      ("D", [])
    ]