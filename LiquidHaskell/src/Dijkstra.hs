{-# LANGUAGE ScopedTypeVariables #-}
{-@ LIQUID "--exact-data-con" @-}
-- {-@ LIQUID "--no-totality" @-}
-- {-@ LIQUID "--no-termination" @-}
-- {-@ LIQUID "--totality" @-}

module Dijkstra where

-- https://mmhaskell.com/blog/2022/8/22/dijkstras-algorithm-in-haskell

import Data.Maybe (fromMaybe)
import MinHeap as H (MinHeap, extractMin, fromList, insert)

type HashMap k v = [(k, v)]

lookupHashMap :: Eq k => k -> HashMap k v -> Maybe v
lookupHashMap _ [] = Nothing
lookupHashMap key ((k, v):rest)
    | key == k  = Just v
    | otherwise = lookupHashMap key rest

type HashSet a = [a]

{-@ data Distance = Dist Int | Infinity @-}
data Distance = Dist Int | Infinity
  deriving (Show, Ord, Eq)

{-@ measure isValidDistance @-}
isValidDistance :: Distance -> Bool
isValidDistance (Dist v) = v >= 0
isValidDistance Infinity = True

{-@ type ValidDistance = {v:Distance | isValidDistance v} @-}

elemInGraph :: String -> Graph -> Bool
elemInGraph node graph = case lookupHashMap node (edges graph) of
  Just _ -> True
  Nothing -> False

elemInHashMap :: (Eq k) => k -> HashMap k v -> Bool
elemInHashMap node hMap = case lookupHashMap node hMap of
  Just _ -> True
  Nothing -> False

{-@ addDist :: ValidDistance -> ValidDistance -> ValidDistance @-}
addDist :: Distance -> Distance -> Distance
addDist (Dist x) (Dist y) = Dist (x + y)
addDist _ _ = Infinity

{-@ (!??) :: (Eq k) => HashMap k ValidDistance -> k -> ValidDistance @-}
-- {-@ (!??) :: (Eq k) => m:HashMap k ValidDistance -> l:k -> {v:ValidDistance | (elemInHashMap l m)} @-}
(!??) :: (Eq k) => HashMap k Distance -> k -> Distance
(!??) m key = fromMaybe Infinity (lookup key m)

{-@ data Graph = Graph { edges :: HashMap String [(String, {x:Int | x >= 0})] } @-}
newtype Graph = Graph
  {edges :: HashMap String [(String, Int)]}

{-@ type NodeInGraph g = {s:String | True } @-} -- elemInGraph s g} @-} -- member v (edges g)} @-}


{-@ data DijkstraState = DijkstraState
    { visitedSet  :: HashSet String
    , distanceMap :: HashMap String ValidDistance
    , nodeQueue   :: MinHeap ValidDistance String
    }
  @-}
data DijkstraState = DijkstraState
  { visitedSet :: HashSet String,
    distanceMap :: HashMap String Distance,
    nodeQueue :: MinHeap Distance String
  }
  deriving (Show)

{-@ findShortestDistance :: g:Graph -> (NodeInGraph g) -> (NodeInGraph g) -> ValidDistance @-}
findShortestDistance :: Graph -> String -> String -> Distance
findShortestDistance graph src dest = processQueue initialState !?? dest
  where
    initialVisited = []
    initialDistances = [(src, Dist 0)]
    initialQueue = H.fromList [(Dist 0, src)]
    initialState = DijkstraState initialVisited initialDistances initialQueue

    {-@ lazy processQueue @-}
    {-@ processQueue :: (Eq k) => DijkstraState -> HashMap String ValidDistance @-}
    processQueue :: DijkstraState -> HashMap String Distance
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
                    unvisitedNeighbors = filter (\(n, _) -> n `notElem` v1) allNeighbors
                 in -- Fold each neighbor and recursively process the queue
                    processQueue $ foldl (foldNeighbor node) (DijkstraState v1 d0 q1) unvisitedNeighbors

    {-@ foldNeighbor :: String -> DijkstraState -> (String, {x:Int | x >= 0}) -> DijkstraState @-}
    foldNeighbor :: String -> DijkstraState -> (String, Int) -> DijkstraState
    foldNeighbor current ds@(DijkstraState v1 d0 q1) (neighborNode, cost) =
      let altDistance = addDist (d0 !?? current) (Dist cost)
       in if altDistance < d0 !?? neighborNode
            then DijkstraState v1 ((neighborNode, altDistance) : d0) (H.insert (altDistance, neighborNode) q1)
            else ds

-- Example graph
graph1 :: Graph
graph1 =
  Graph
    [ ("A", [("D", 100), ("B", 1), ("C", 20)]),
      ("B", [("D", 50)]),
      ("C", [("D", 20)]),
      ("D", [])
    ]













    
-- module Blank where

-- {-@ type IsValidDist = {v: Int | v >= 0 } @-}

-- {-@ addDist :: x:IsValidDist -> y:IsValidDist -> {z:IsValidDist | z == x + y } @-}
-- addDist :: Int -> Int -> Int
-- addDist x y = x + y


-- data Distance = Dist Int | Infinity

-- {-@ measure isValid :: Distance -> Bool @-}
-- isValid :: Distance -> Bool 
-- isValid (Dist d) = d >= 0
-- isValid Infinity = True

-- {-@ type IsValidDist = {v: Distance | isValid v } @-}

-- {-@ measure compareValidDistances :: Distance  -> Distance  -> Bool @-}
-- compareValidDistances ::  Distance  -> Distance  -> Bool
-- compareValidDistances (Dist v1) (Dist v2) = v1 >= v2
-- compareValidDistances Infinity  _         = True
-- compareValidDistances _         Infinity  = True
-- compareValidDistances _         _         = False

-- {-@ predicate IsEqual Z X Y = compareValidDistances Z X && compareValidDistances Z Y @-}

-- {-@ addDist :: x:IsValidDist -> y:IsValidDist -> {z:IsValidDist | IsEqual z x y } @-}
-- addDist :: Distance -> Distance -> Distance
-- addDist (Dist x) (Dist y) = Dist (x + y)
-- addDist _       _       = Infinity

-- {-@ invariant {d:Distance | isValid d <=> (d == Infinity || distanceValue d >= 0)} @-}

