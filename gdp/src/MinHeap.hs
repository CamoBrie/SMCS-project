{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module MinHeap
  ( MinHeap,
    Sized,
    fromList,
    insert,
    merge,
    extractMin,
    isEmpty,
  )
where

import GHC.TypeLits

--- GDP Stuff
data Sized (n :: Nat) a = Sized a

--- MinHeap Stuff
data MinHeap k a
  = Leaf
  | Node a (MinHeap k a) (MinHeap k a) k

instance (Show a, Show k) => Show (MinHeap k a) where
  show Leaf = "Leaf"
  show (Node a l r k) = concat ["Node ", show a, " ", show k, " (", show l, ") (", show r, ")"]

instance (Show (MinHeap k a)) => Show (Sized n (MinHeap k a)) where
  show (Sized h) = show h

-- | Create a new heap from a list of key-value pairs.
-- GDP invariants:
-- 1. The keys in the heap are sorted
-- 2. The size of the heap is equal to the length of the list
-- Create a new heap with a known size.
fromList :: forall k a r. (Ord k) => [(k, a)] -> (forall n. Sized n (MinHeap k a) -> r) -> r
fromList xs k = k (Sized (fromList' xs) :: Sized n (MinHeap k a))

fromList' :: (Ord k) => [(k, a)] -> MinHeap k a
fromList' = foldr insert' Leaf

-- | Insert a new key-value pair into the heap.
-- GDP invariants:
-- 1. The keys in the heap are sorted
-- 2. The size of the heap is increased by 1
insert :: (Ord k) => (k, a) -> Sized n (MinHeap k a) -> Sized (n) (MinHeap k a)
insert (k, a) (Sized h) = Sized (insert' (k, a) h)

insert' :: (Ord k) => (k, a) -> MinHeap k a -> MinHeap k a
insert' (k, a) h = merge' h (Node a Leaf Leaf k)

-- | Merge two heaps into one.
-- GDP invariants:
-- 1. The keys in the heap are sorted
-- 2. The size of the heap is increased by the sum of the sizes of the input heaps
merge :: (Ord k) => Sized n (MinHeap k a) -> Sized m (MinHeap k a) -> Sized (n + m) (MinHeap k a)
merge (Sized h1') (Sized h2') = Sized (merge' h1' h2')

merge' :: (Ord k) => MinHeap k a -> MinHeap k a -> MinHeap k a
merge' h Leaf = h
merge' Leaf h = h
merge' h1@(Node a1 l1 r1 k1) h2@(Node a2 l2 r2 k2)
  | k1 <= k2 = Node a1 (merge' h2 r1) l1 k1
  | otherwise = Node a2 (merge' h1 r2) l2 k2

-- | Extract the minimum key-value pair from the heap.
-- GDP invariants:
-- 1. The keys in the heap are sorted
-- 2. The size of the heap is reduced by 1
extractMin :: (Ord k) => Sized (n) (MinHeap k a) -> Maybe ((k, a), Sized n (MinHeap k a))
extractMin (Sized h) = case extractMin' h of
  Nothing -> Nothing
  Just (x, h') -> Just (x, Sized h')

extractMin' :: (Ord k) => MinHeap k a -> Maybe ((k, a), MinHeap k a)
extractMin' Leaf = Nothing
extractMin' (Node a l r k) = Just ((k, a), merge' l r)

isEmpty :: Sized n (MinHeap k a) -> Bool
isEmpty (Sized Leaf) = True
isEmpty _ = False