{-@ LIQUID "--exact-data-con" @-}
{-@ LIQUID "--no-totality" @-}
{-@ LIQUID "--no-termination" @-}

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

{-@ data MinHeap k a   = Leaf
                  | Node { root  :: a
                          , val   :: k
                         , left  :: VMinHeap k a val
                         , right :: VMinHeap k a val 
                          } @-}

{-@ type VMinHeap k a X = MinHeap {v:k | X <= v} a        @-}

{-@ type NonEmptyMinHeap k a = {v:MinHeap k a | not (isEmpty v)} @-}

{-@ measure isEmpty @-}
isEmpty :: MinHeap k a -> Bool
isEmpty Leaf = True
isEmpty _    = False

data MinHeap k a = Leaf
           | Node { root  :: a
                  , val   :: k
                  , left  :: MinHeap k a
                  , right :: MinHeap k a
                  }


instance (Show a, Show k) => Show (MinHeap k a) where
  show Leaf = "Leaf"
  show (Node a _ _ k) = "Node " ++ show a ++ " " ++ show k

fromList :: (Ord k) => [(k, a)] -> MinHeap k a
fromList = foldr insert Leaf

{-@ insert :: (Ord k) => (k, a) -> MinHeap k a -> MinHeap k a @-}
insert :: (Ord k) => (k, a) -> MinHeap k a -> MinHeap k a
insert (k, a) h = merge h (Node a k Leaf Leaf)

{-@ merge ::Ord k => MinHeap k a -> MinHeap k a -> MinHeap k a  @-}
merge :: (Ord k) => MinHeap k a -> MinHeap k a -> MinHeap k a
merge h Leaf = h
merge Leaf h = h
merge h1@(Node a1 k1 l1 r1 ) h2@(Node a2 k2 l2 r2 )
  | k1 <= k2 = Node a1 k1 (merge h2 r1) l1 
  | otherwise = Node a2 k2 (merge h1 r2) l2

extractMin :: (Ord k) => MinHeap k a -> Maybe ((k, a), MinHeap k a)
extractMin Leaf = Nothing
extractMin (Node a k l r) = Just ((k, a), merge l r)