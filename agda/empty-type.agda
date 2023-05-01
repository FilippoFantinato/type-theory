module empty-type where

open import natural-numbers

data ∅ : Set where

-- Fact that there is no element in empty set
claim : (ℕ → ∅) → ∅
claim f = f zero
