module dijkstra where

open import Data.Bool using (if_then_else_ ; true ; false; not)
open import Data.Nat
open import Data.Maybe
open import Data.Product
open import Data.List  using (List; _∷_; [] ; filter)
open import Data.Tree.AVL.Map as Map
open import Data.Tree.AVL.Sets as Set
open import Data.Nat.Properties using (<-strictTotalOrder)

open import minheap as MH
open import distance

NodeDist = ℕ × Distance

open module DH = MH NodeDist _≤ND_
open module S = Set <-strictTotalOrder
open module M = Map <-strictTotalOrder


testGraph : List (ℕ × List NodeDist)
testGraph = (( 1 , (2 , D 10 ) ∷ (3 , D 2 ) ∷  []) 
            ∷ (2 , (1 , D 20 ) ∷ [] )
            ∷ (3 , (2 , D 10 ) ∷ [] )
            ∷ [])

Graph = M.Map (List NodeDist) 

test2 : Graph
test2 = M.fromList testGraph

record DijkstraState : Set where
    constructor mkState
    field
        visited   : S.⟨Set⟩ 
        distances : M.Map Distance
        queue     : DH.SkewHeap NodeDist

lookupDistance : ℕ → M.Map Distance → Distance
lookupDistance n m = fromMaybe ∞ (M.lookup n m)

foldNeighbor : ℕ → DijkstraState → NodeDist → DijkstraState
foldNeighbor current (mkState visited distances queue) (neighborNode , cost)
        -- if alternative is better
    = if altDistance ≤D thisDistance
        -- then add new distance to distance map and to priority queue
        then mkState visited 
                (M.insert neighborNode altDistance distances)  -- updated distance map
                (DH.insert (neighborNode , altDistance) queue) -- updated priority queue
        -- else do nothing
        else mkState visited distances queue
    where altDistance  = addDist (lookupDistance current distances) cost
          thisDistance = lookupDistance neighborNode distances



{-# TERMINATING #-}
dijkstra' : Graph → DijkstraState → DijkstraState
dijkstra' g (mkState visited distances DH.Empty) = mkState visited distances DH.Empty
dijkstra' g (mkState visited distances (DH.SkewNode (n , dist) l r)) with (n S.∈? visited)
... | true  = dijkstra' g (mkState visited distances (l DH.⊎ r) )
... | false = dijkstra' g (mkState (S.insert n visited) {!   !} (DH.insert {!   !} (l DH.⊎ r) ) )
                where 
                      allNbs : List NodeDist
                      allNbs = fromMaybe [] (M.lookup n g)
                      unvisitedNbs : List NodeDist
                      unvisitedNbs = filter (λ (x , _ ) → {!   !} (not (x S.∈? visited))) allNbs

initialState : ℕ → DijkstraState
initialState n =  mkState S.empty
                          (M.singleton n (D 0))
                          (DH.singleton ((n , D 0)))

-- dijkstra : Graph → ℕ → M.Map Distance
-- dijkstra g n =  dijkstra' g (initialState n)