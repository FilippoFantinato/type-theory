module lists where

open import natural-numbers


data List (X : Set) : Set where
  []   : List X
  _::_ : X → List X → List X


exampleListℕ : List
exampleListℕ = zero :: ((succ (succ zero)) :: ((succ zero) :: []))


