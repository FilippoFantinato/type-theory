module types.empty where

open import types.natural-numbers


data ⊥ : Set where

-- Fact that there is no element in empty set
claim : (ℕ → ⊥) → ⊥
claim f = f zero


¬ : Set → Set
¬ X = (X → ⊥)

