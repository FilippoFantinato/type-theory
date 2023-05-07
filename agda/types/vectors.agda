module types.vectors where

open import types.natural-numbers


data Vector (A : Set) : ℕ → Set where
  [] : Vector A zero
  _∷_ : {n : ℕ} → A → Vector A n → Vector A (succ n)
