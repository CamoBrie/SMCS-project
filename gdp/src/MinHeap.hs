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

import Data.Foldable
import Data.Refined
import Data.The
import Logic.Proof
import Logic.Propositional
import Theory.Named

--- MinHeap Stuff
data MinHeap k a
  = Leaf
  | Node a (MinHeap k a) (MinHeap k a) k
  deriving (Show)

-- | Create a new heap from a list of key-value pairs.
fromList :: (Ord k) => [(k, a)] -> Maybe (MinHeap k a)
fromList = foldrM f Leaf
  where
    f :: (Ord k) => (k, a) -> (MinHeap k a) -> Maybe (MinHeap k a)
    f v h = name h $ \h' -> do
      proof <- isValidMinHeap h'
      insert v (h' ... proof)

-- | Insert a new key-value pair into the heap.
-- Preconditions:
-- 1. The heap is a valid min-heap
insert :: (Ord k) => (k, a) -> (MinHeap k a ~~ h ::: IsValidMinHeap h) -> Maybe (MinHeap k a)
insert (k, a) h = name (Node a Leaf Leaf k) $ \h' -> do
  p <- isValidMinHeap h'
  mr <- merge (h' ... p) h
  Just $ mr

-- | Merge two heaps into one.
-- Preconditions:
-- 1. Both heaps are valid min-heaps
merge :: (Ord k) => (MinHeap k a ~~ h1 ::: IsValidMinHeap h1) -> (MinHeap k a ~~ h2 ::: IsValidMinHeap h2) -> Maybe (MinHeap k a)
merge (The h) (The Leaf) = Just h
merge (The Leaf) (The h) = Just h
merge h1@(The (Node a1 l1 r1 k1)) h2@(The (Node a2 l2 r2 k2))
  | k1 <= k2 = name r1 $ \r1' -> do
      p <- isValidMinHeap r1'
      mr <- merge (r1' ... p) h2
      Just $ Node a1 l1 mr k1
  | otherwise = name r2 $ \r2' -> do
      p <- isValidMinHeap r2'
      mr <- merge h1 (r2' ... p)
      Just $ Node a2 l2 mr k2

-- | Extract the minimum key-value pair from the heap.
-- Preconditions:
-- 1. The heap is not empty
-- 2. The heap is a valid min-heap
extractMin :: (Ord k) => (MinHeap k a ~~ h ::: IsNotEmpty h /\ IsValidMinHeap h) -> ((k, a), MinHeap k a)
extractMin (The (Node a l r k)) = name2 l r $ \l' r' -> case do
  pl <- isValidMinHeap l'
  pr <- isValidMinHeap r'
  (merge (l' ... pl) (r' ... pr)) of
  Just h -> ((k, a), h)
  Nothing -> error "impossible" -- merge should always return a valid min-heap, if both inputs are valid min-heaps

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
