open import Data.Bool
module minheap (A : Set)(_≤A_ : A → A → Bool) where

open import Data.Nat 
open import Data.Nat.Properties
open import Data.Maybe
open import Data.Product
open import Relation.Binary.PropositionalEquality.Core using (_≡_; cong; subst)
open import Relation.Binary.PropositionalEquality.TrustMe using (trustMe)


data SkewHeap A : Set where 
    Empty    : SkewHeap A 
    SkewNode : (x : A) → SkewHeap A → SkewHeap A → SkewHeap A

{-# TERMINATING #-}
_⊎_ :  SkewHeap A → SkewHeap A → SkewHeap A
h₁@(SkewNode x₁ l₁ r₁) ⊎ h₂@(SkewNode x₂ l₂ r₂) with x₁ ≤A x₂
... | false  = SkewNode x₁ (h₂ ⊎ r₁) l₁
... | true   = SkewNode x₂ (r₁ ⊎ h₂) l₂
Empty ⊎ h = h
h ⊎ Empty = h


extractMin : SkewHeap A → Maybe ( A × SkewHeap A)
extractMin Empty = nothing
extractMin (SkewNode x l r ) = just (x , l ⊎ r )

singleton : A → SkewHeap A
singleton x = SkewNode x Empty Empty

insert : A → SkewHeap A → SkewHeap A
insert x h = singleton x ⊎ h

