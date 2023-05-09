module types.positive where

open import types.natural-numbers


-- data Positive : ℕ → Set where
--   positive-one : Positive (succ zero)
--   positive-succ : {n : ℕ} → (Positive n) → Positive (succ n)


data Positive : ℕ → Set where
  positive-succ : (n : ℕ) → (Positive (succ n))
