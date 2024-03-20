module dijkstra where

open import Data.Bool 
open import Data.Nat
open import Data.Maybe
open import Data.Product
open import Data.List  using (List; _∷_; [] ; filter ; foldl)
open import Data.Tree.AVL.Map as Map
open import Data.Tree.AVL.Sets as Set
open import Data.Nat.Properties using (<-strictTotalOrder)
open import Relation.Nullary 
-- open import Data.Bool.Properties ((T?))

open import minheap as MH
open import distance

NodeDist = ℕ × Distance

open module DH = MH NodeDist _≤ND_
open module S = Set <-strictTotalOrder
open module M = Map <-strictTotalOrder


testGraph : List (ℕ × List NodeDist)
testGraph = (( 1 , (2 , D 10 ) ∷ (3 , D 2 ) ∷ [] ) 
            ∷ (2 , (1 , D 20 ) ∷ (4 , D 3 ) ∷ [] )
            ∷ (3 , (2 , D 5 )  ∷ (4 , D 10) ∷ [] )
            ∷ (4 , [])
            ∷ [])

Graph = M.Map (List NodeDist) 

test1 : Graph
test1 = M.fromList testGraph

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
dijkstra' g s@(mkState _ _ DH.Empty) = s
dijkstra' g   (mkState v0 d0 q0@(DH.SkewNode (n , dist) l r)) with (n S.∈? v0) 
... | true  = dijkstra' g (mkState v0 d0 (l DH.⊎ r) )
... | false = dijkstra' g s1
                where 
                      allNbs : List NodeDist
                      allNbs = fromMaybe [] (M.lookup n g)
                      unvisitedNbs : List NodeDist
                      unvisitedNbs = filter (λ (x , _ ) → T? (not (n S.∈? v0))) allNbs
                      v1 = S.insert n v0
                      q1 = l DH.⊎ r
                      s1 : DijkstraState
                      s1 = foldl (foldNeighbor n) (mkState v1 d0 q1) unvisitedNbs 

initialState : ℕ → DijkstraState
initialState n =  mkState S.empty
                          (M.singleton n (D 0))
                          (DH.singleton ((n , D 0)))

dijkstra : Graph → ℕ → DijkstraState
dijkstra g n = dijkstra' g (initialState n) 


-- test
example1 : M.Map Distance
example1 = M.toList $ DijkstraState.distances (dijkstra test1 1)
