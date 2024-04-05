{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module MinHeap (fromList, insert, merge, extractMin, MinHeap, isEmpty, classifyHeapNotEmpty, isValidMinHeap) where

import Data.Foldable (foldrM)
import Data.Refined (conjure, exorcise, (...), type (:::))
import Data.The
import Logic.Proof (Proof, axiom)
import Logic.Propositional (elimAndR, introAnd, type (/\))
import Theory.Named (name, name2, type (~~))

--- MinHeap Stuff
data MinHeap k a
  = Leaf
  | Node a (MinHeap k a) (MinHeap k a) k
  deriving (Show)

instance (Eq a, Eq k) => Eq (MinHeap k a) where
  Leaf == Leaf = True
  (Node a1 l1 r1 k1) == (Node a2 l2 r2 k2) = a1 == a2 && k1 == k2 && l1 == l2 && r1 == r2
  _ == _ = False

-- | Create a new heap from a list of key-value pairs.
fromList :: (Ord k, Eq a) => [(k, a)] -> Maybe (MinHeap k a)
fromList = foldrM f Leaf
  where
    f :: (Ord k, Eq a) => (k, a) -> (MinHeap k a) -> Maybe (MinHeap k a)
    f v h = name h $ \h' -> do
      proof <- isValidMinHeap h'
      return $ insert v (h' ... proof)

-- | Insert a new key-value pair into the heap.
-- Preconditions:
-- 1. The heap is a valid min-heap
insert :: (Ord k, Eq a) => (k, a) -> (MinHeap k a ~~ h ::: IsValidMinHeap h) -> (MinHeap k a)
insert (k, a) h = name (Node a Leaf Leaf k) $ \h' -> merge (h' ... axiom) h

-- | Merge two heaps into one.
-- Preconditions:
-- 1. Both heaps are valid min-heaps
merge :: (Ord k, Eq a) => (MinHeap k a ~~ h1 ::: IsValidMinHeap h1) -> (MinHeap k a ~~ h2 ::: IsValidMinHeap h2) -> (MinHeap k a)
merge (The h) (The Leaf) = h
merge (The Leaf) (The h) = h
merge h1@(The (Node a1 l1 r1 k1)) h2@(The (Node a2 l2 r2 k2))
  | k1 <= k2 = name r1 $ \r1' ->
      let pr = subHeapValid h1 r1'
       in Node a1 l1 (merge (r1' ... pr) h2) k1
  | otherwise = name r2 $ \r2' ->
      let pr = subHeapValid h2 r2'
       in Node a2 l2 (merge h1 (r2' ... pr)) k2
merge _ _ = error "merge: invalid heap" -- impossible

-- | Extract the minimum key-value pair from the heap.
-- Preconditions:
-- 1. The heap is not empty
-- 2. The heap is a valid min-heap
extractMin :: (Ord k, Eq a) => (MinHeap k a ~~ h ::: IsNotEmpty h /\ IsValidMinHeap h) -> ((k, a), MinHeap k a)
extractMin h@(The (Node a l r k)) = name2 l r $ \l' r' ->
  let pl = subHeapValid (elimAnd h) l'
      pr = subHeapValid (elimAnd h) r'
   in ((k, a), (merge (l' ... pl)) (r' ... pr))
extractMin _ = error "extractMin: invalid heap" -- impossible

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
    smallerThan _ _ = error "smallerThan: invalid heap" -- impossible
isValidMinHeap _ = error "isValidMinHeap: invalid heap" -- impossible

-- | Prove that a subheap is valid.
subHeapValid :: (Eq a, Eq k) => (MinHeap k a ~~ h ::: IsValidMinHeap h) -> (MinHeap k a ~~ l) -> Proof (IsValidMinHeap l)
subHeapValid (The (Node _ lh rh _)) (The l) = case lh == l of
  True -> axiom
  False -> case rh == l of
    True -> axiom
    False -> error "subHeapValid: invalid subheap" -- impossible
subHeapValid _ _ = error "subHeapValid: invalid heap" -- impossible

-- | convert big proof to small
elimAnd :: (MinHeap k a ~~ h ::: IsNotEmpty h /\ IsValidMinHeap h) -> (MinHeap k a ~~ h ::: IsValidMinHeap h)
elimAnd h = exorcise h ... elimAndR (conjure h)