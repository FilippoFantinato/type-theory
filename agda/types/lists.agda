module types.lists where

open import types.natural-numbers
open import types.equality


data List (X : Set) : Set where
  []   : List X
  _∷_ : X → List X → List X


data _≈_ {A : Set} : List A → List A → Set where
  both-empty     : [] ≈ []
  both-same-cons : {xs ys : List A} {x y : A} → x ≡ y → xs ≈ ys → (x ∷ xs) ≈ (y ∷ ys)
