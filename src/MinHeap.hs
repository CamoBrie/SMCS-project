module MinHeap
  ( MinHeap,
    fromList,
    insert,
    merge,
    extractMin,
  )
where

-- https://github.com/nytr0gen/hs-min-heap/blob/master/MinHeap.hs

import Prelude hiding (head, length, null, tail)

data MinHeap k a
  = Leaf
  | Node a (MinHeap k a) (MinHeap k a) k

instance (Show a, Show k) => Show (MinHeap k a) where
  show Leaf = "Leaf"
  show (Node a _ _ k) = "Node " ++ show a ++ " " ++ show k

fromList :: (Ord k) => [(k, a)] -> MinHeap k a
fromList = foldr insert Leaf

insert :: (Ord k) => (k, a) -> MinHeap k a -> MinHeap k a
insert (k, a) h = merge h (Node a Leaf Leaf k)

merge :: (Ord k) => MinHeap k a -> MinHeap k a -> MinHeap k a
merge h Leaf = h
merge Leaf h = h
merge h1@(Node a1 l1 r1 k1) h2@(Node a2 l2 r2 k2)
  | k1 <= k2 = Node a1 (merge h2 r1) l1 k1
  | otherwise = Node a2 (merge h1 r2) l2 k2

extractMin :: (Ord k) => MinHeap k a -> Maybe ((k, a), MinHeap k a)
extractMin Leaf = Nothing
extractMin (Node a l r k) = Just ((k, a), merge l r)