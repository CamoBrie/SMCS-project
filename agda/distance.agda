module distance where
open import Data.Product
open import Data.Nat
open import Data.Bool

data Distance : Set where
    ∞ : Distance
    D : ℕ → Distance

_≤D_ : Distance → Distance → Bool
∞ ≤D ∞ = true
∞ ≤D _ = false
_ ≤D ∞ = true
(D x) ≤D (D y) = x ≤ᵇ y

addDist : Distance → Distance → Distance
addDist (D x) (D y) = D (x + y)
addDist _ _ = ∞

_≤ND_ : (ℕ × Distance) → (ℕ × Distance) → Bool
(_ , d) ≤ND (_ , e) = (d ≤D e)

