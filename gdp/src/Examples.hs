module Examples where

import Data.Refined ((...))
import Dijkstra (Distance (..), Graph (..), classifyDistancePositiveGraph, classifyGraph, classifyNodeInGraph, dijkstra)
import Logic.Propositional (introAnd)
import Theory.Named (name3)

runDijkstra :: Graph -> String -> String -> Maybe Int
runDijkstra g s e = name3 g s e $ \g' s' e' -> case do
  (validGraph) <- classifyGraph g'
  (validPositive) <- classifyDistancePositiveGraph g'
  (validStart) <- classifyNodeInGraph s' g'
  (validEnd) <- classifyNodeInGraph e' g'

  return $ dijkstra (s' ... validStart) (e' ... validEnd) (g' ... (validGraph `introAnd` validPositive)) of
  Just ((Dist d)) -> Just d
  _ -> Nothing

-- | Example 1: A simple graph with 3 nodes.
example1 :: Graph
example1 =
  Graph $
    [ ("A", [("C", 4)]),
      ("B", [("A", 1)]),
      ("C", [("A", 2), ("B", 3)])
    ]

-- | Example 2: A bigger graph
example2 :: Graph
example2 =
  Graph $
    [ ("A", [("B", 1), ("C", 4), ("D", 6)]),
      ("B", [("C", 2), ("D", 5)]),
      ("C", [("D", 1)]),
      ("D", [])
    ]

-- | Example 3: A graph with negative weights
-- This graph is invalid because it has negative weights.
example3 :: Graph
example3 =
  Graph $
    [ ("A", [("B", 1), ("C", -4), ("D", 6)]),
      ("B", [("C", 2), ("D", 5)]),
      ("C", [("D", 1)]),
      ("D", [])
    ]

-- | Example 4: A graph with invalid nodes
-- This graph is invalid because it has a node that is not in the graph.
example4 :: Graph
example4 =
  Graph $
    [ ("A", [("B", 1), ("C", 4), ("E", 6)]),
      ("B", [("C", 2), ("D", 5)]),
      ("C", [("D", 1)]),
      ("D", [])
    ]

-- | Example 5: A huge complex graph
example5 :: Graph
example5 =
  Graph $
    [ ("A", [("B", 1), ("C", 4), ("D", 6)]),
      ("B", [("C", 2), ("D", 5), ("E", 3)]),
      ("C", [("D", 1)]),
      ("D", []),
      ("E", [("F", 1), ("G", 4), ("H", 6)]),
      ("F", [("G", 2), ("H", 5)]),
      ("G", [("H", 1)]),
      ("H", [])
    ]