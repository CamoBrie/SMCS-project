-- {-@ LIQUID "--exact-data-con" @-}
-- {-@ LIQUID "--no-totality" @-}
-- {-@ LIQUID "--no-termination" @-}

module MinHeap
  ( MinHeap,
    fromList,
    insert,
    merge,
    extractMin,
  )
where

-- https://github.com/nytr0gen/hs-min-heap/blob/master/MinHeap.hs

import Prelude hiding (head, length, null, tail,max)

{-@ type VMinHeap k a X = { v: MinHeap k a | isMinHeap v X } @-}

{-@ measure isMinHeap :: (Ord k) => MinHeap k a -> k -> Bool @-}
isMinHeap :: Ord k => MinHeap k a -> k -> Bool
isMinHeap heap key = case heap of
  Leaf           -> True
  (Node _ k l r) -> key <= k && isMinHeap l k && isMinHeap r k

{-@ type NonEmptyMinHeap k a = {v:MinHeap k a | not (isEmpty v)} @-}

{-@ measure isEmpty @-}
isEmpty :: MinHeap k a -> Bool
isEmpty Leaf = True
isEmpty _    = False

-- {-@ data MinHeap k a = Leaf
--                      | Node { root  :: a
--                             , val   :: k
--                             , left  :: VMinHeap k a val  
--                             , right :: VMinHeap k a val  
--                             } 
-- @-}
{-@ data MinHeap k a = Leaf
                     | Node { root  :: a
                            , val   :: k
                            , left  :: MinHeap k a 
                            , right :: MinHeap k a 
                            } 
  @-}
data MinHeap k a = Leaf
                  | Node { root  :: a
                         , val   :: k
                         , left  :: MinHeap k a
                         , right :: MinHeap k a
                  }
              deriving(Ord,Eq)

instance Foldable (MinHeap k) where
  foldMap _ Leaf = mempty
  foldMap f (Node root _ left right) =
      foldMap f left `mappend`
      f root `mappend`
      foldMap f right


instance (Show a, Show k) => Show (MinHeap k a) where
  show Leaf           = "Leaf"
  show (Node a _ _ k) = "Node " ++ show a ++ " " ++ show k


{-@ measure isCorrect :: (Ord k, Ord a) => [(k, a)] -> MinHeap k a-> Bool @-}
isCorrect :: (Ord k, Ord a) => [(k, a)] -> MinHeap k a -> Bool
isCorrect x h = listLength x == heapLength h && isEqual x h


{-@ measure listLength :: (Ord k, Ord a) => [(k, a)] -> Int @-}
listLength :: (Ord k, Ord a) => [(k, a)] -> Int
listLength []     = 0
listLength (_:xs) = 1 + listLength xs

{-@ measure toList :: (Ord k, Ord a) => MinHeap k a -> [(k, a)] @-}
toList :: (Ord k, Ord a) => MinHeap k a -> [(k, a)]
toList Leaf           = []
toList (Node a k l r) = toList l ++ [(k, a)] ++ toList r

{-@ measure isEqual :: (Ord k, Ord a) => [(k,a)] -> MinHeap k a -> Bool @-}
isEqual :: (Ord k, Ord a) => [(k,a)] -> MinHeap k a -> Bool
isEqual xs heap = foldr (\x acc -> x `elem` xs && acc) True (toList heap)

areElements :: (Ord k, Ord a) => MinHeap k a -> MinHeap k a -> Bool
areElements h1 h2 = foldr (\x acc -> x `elem` h2 && acc) True h1

{-@ fromList :: (Ord k,Ord a) => xs:[(k, a)] -> {v:MinHeap k a | True } @-} -- isCorrect xs v} @-} 
fromList :: (Ord k, Ord a) => [(k, a)] -> MinHeap k a
fromList = foldr insert Leaf

-- {-@ insert :: (Ord k, Ord a) 
--            => (k, a) 
--            -> v1:MinHeap k a 
--            -> {v: NonEmptyMinHeap k a | (heapLength v == ((heapLength v1) + 1))} 
--   @-}
insert :: (Ord k, Ord a) => (k, a) -> MinHeap k a -> MinHeap k a
insert (k, a) h = merge h (Node a k Leaf Leaf)

-- {-@ merge :: (Ord k, Ord a) 
--           => h1:MinHeap k a 
--           -> h2:MinHeap k a 
--           -> {v:MinHeap k a | heapLength v == (heapLength h1 + heapLength h2 - 1) 
--                             && areElements h1 v 
--                             && areElements h2 v}  
--   @-}
{-@ lazy merge @-}
{-@ merge :: (Ord k, Ord a) => MinHeap k a -> MinHeap k a -> MinHeap k a @-}
merge :: (Ord k, Ord a) => MinHeap k a -> MinHeap k a -> MinHeap k a
merge h Leaf = h
merge Leaf h = h
merge h1@(Node a1 k1 l1 r1 ) h2@(Node a2 k2 l2 r2 )
  | k1 <= k2  = Node a1 k1 (merge h2 r1) l1 
  | otherwise = Node a2 k2 (merge h1 r2) l2

-- {-@ areElements :: (Ord k, Ord a) => MinHeap k a -> MinHeap k a -> Bool  @-}
-- areElements :: (Ord k, Ord a) => MinHeap k a -> MinHeap k a -> Bool
-- areElements Leaf Leaf = True
-- areElements Leaf _ = False
-- areElements (Node k v l r) h2 = l == h2 || r == h2 --|| areElements l h2 || areElements r h2

-- {-@ predicate Lee H G = ((heapLength H) < (heapLength G)) @-}

-- {-@ isSmaller :: (Ord k, Ord a) => MinHeap k a -> MinHeap k a -> Bool@-}
-- isSmaller :: (Ord k, Ord a) => MinHeap k a -> MinHeap k a -> Bool
-- isSmaller x y = heapLength x < heapLength y

{-@ lazy heapLength @-}
{-@ measure heapLength :: MinHeap k a -> Int @-}
heapLength :: MinHeap k a -> Int
heapLength Leaf           = 0
heapLength (Node _ _ l r) = 1 + nodeHeight l r

{-@ lazy nodeHeight @-}
{-@ measure nodeHeight :: MinHeap k a -> MinHeap k a -> Int @-}
nodeHeight :: MinHeap k a -> MinHeap k a -> Int
nodeHeight l r = 1 + max hl hr
  where
    hl         = heapLength l
    hr         = heapLength r
    
{-@ inline max @-}
max :: Int -> Int -> Int
max x y = if x > y then x else y

-- {-@ outputSmaller :: (Ord k, Ord a) => xs:NonEmptyMinHeap k a -> {ys:MinHeap k a | heapLength ys < heapLength xs} @-}
-- outputSmaller :: (Ord k, Ord a) => MinHeap k a -> MinHeap k a
-- outputSmaller Leaf = Leaf 
-- outputSmaller (Node _ _ l r) = r

-- {-@ extractMin :: (Ord k, Ord a) 
--                => h:NonEmptyMinHeap k a 
--                -> Maybe ((k,a),{v: MinHeap k a | heapLength v <= heapLength h}) 
--   @-}
{-@ extractMin :: (Ord k, Ord a) => h:NonEmptyMinHeap k a -> Maybe ((k,a),MinHeap k a) @-}
extractMin :: (Ord k, Ord a) => MinHeap k a -> Maybe ((k, a), MinHeap k a)
extractMin Leaf           = Nothing
extractMin (Node a k l r) = Just ((k, a), merge l r)