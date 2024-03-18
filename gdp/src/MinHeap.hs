{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module MinHeap (fromList, insert, merge, extractMin, MinHeap (..), isEmpty, classifyHeapNotEmpty, isValidMinHeap) where

import Data.Refined (type (:::))
import Data.The
import Logic.Proof (Proof, axiom)
import Logic.Propositional (introAnd, type (/\))
import Theory.Named (name2, type (~~))

--- MinHeap Stuff
data MinHeap k a
  = Leaf
  | Node a (MinHeap k a) (MinHeap k a) k

instance (Show a, Show k) => Show (MinHeap k a) where
  show Leaf = "Leaf"
  show (Node a l r k) = concat ["Node ", show a, " ", show k, " (", show l, ") (", show r, ")"]

-- | Create a new heap from a list of key-value pairs.
fromList :: (Ord k) => [(k, a)] -> MinHeap k a
fromList = foldr insert Leaf

-- | Insert a new key-value pair into the heap.
insert :: (Ord k) => (k, a) -> MinHeap k a -> MinHeap k a
insert (k, a) h = merge h (Node a Leaf Leaf k)

-- | Merge two heaps into one.
merge :: (Ord k) => MinHeap k a -> MinHeap k a -> MinHeap k a
merge h Leaf = h
merge Leaf h = h
merge h1@(Node a1 l1 r1 k1) h2@(Node a2 l2 r2 k2)
  | k1 <= k2 = Node a1 (merge h2 r1) l1 k1
  | otherwise = Node a2 (merge h1 r2) l2 k2

-- | Extract the minimum key-value pair from the heap.
-- Preconditions:
-- 1. The heap is not empty
-- 2. The heap is a valid min-heap
extractMin :: (Ord k) => (MinHeap k a ~~ h ::: IsNotEmpty h /\ IsValidMinHeap h) -> Maybe ((k, a), MinHeap k a)
extractMin (The (Node a l r k)) = Just ((k, a), merge l r)
extractMin _ = Nothing

-- | Check if the heap is empty.
isEmpty :: MinHeap k a -> Bool
isEmpty Leaf = True
isEmpty _ = False

--- GDP Stuff
data IsNotEmpty h

-- | Classify the size of the heap.

classifyHeapNotEmpty :: (MinHeap k a ~~ h) -> Maybe (Proof (IsNotEmpty h))
classifyHeapNotEmpty (The Leaf) = Nothing
classifyHeapNotEmpty _ = Just $ axiom

data IsValidMinHeap h

data SmallerThan k h

isValidMinHeap :: forall k a h. (Ord k) => (MinHeap k a ~~ h) -> Maybe (Proof (IsValidMinHeap h))
isValidMinHeap (The Leaf) = Just axiom
isValidMinHeap (The (Node _ l r k)) = name2 l r $ \l' r' -> do
  pl <- isValidMinHeap l'
  pr <- isValidMinHeap r'
  psl <- smallerThan k l'
  psr <- smallerThan k r'
  return $ validSub $ pl `introAnd` pr `introAnd` psl `introAnd` psr
  where
    validSub :: Proof (IsValidMinHeap l' /\ IsValidMinHeap r' /\ SmallerThan k l' /\ SmallerThan k r') -> Proof (IsValidMinHeap h)
    validSub _ = axiom

    smallerThan :: (Ord k) => k -> (MinHeap k a ~~ l) -> Maybe (Proof (SmallerThan k l))
    smallerThan _ (The Leaf) = Just axiom
    smallerThan k' (The (Node _ _ _ k''))
      | k' <= k'' = Just axiom
      | otherwise = Nothing
