module types.lists where

open import types.natural-numbers
open import types.equality


data List (X : Set) : Set where
  []   : List X
  _∷_ : X → List X → List X


data _≈_ {A : Set} : List A → List A → Set where
  both-empty     : [] ≈ []
  both-same-cons : {xs ys : List A} {x y : A} → x ≡ y → xs ≈ ys → (x ∷ xs) ≈ (y ∷ ys)


data All {A : Set} (P : A → Set) : List A → Set where
  empty : All P []
  const : {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)


data Any {A : Set} (P : A → Set) : List A → Set where
  -- empty : Any P []
  here  : {x : A} {xs : List A} → P x      → Any P (x ∷ xs)
  there : {x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)


data _∈_ {A : Set} : A → List A → Set where
  here : {a : A}    {xs : List A} → a ∈ (a ∷ xs)
  there : {a x : A} {xs : List A} → a ∈ xs → a ∈ (x ∷ xs)
