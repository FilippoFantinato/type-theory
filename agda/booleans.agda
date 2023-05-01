module booleans where

data Bool : Set where
  true  : Bool
  false : Bool

-- Negation
¬_ : Bool → Bool
¬ true = false
¬ false = true

-- AND
_&&_ : Bool → Bool → Bool
_&&_ true y = y
_&&_ false y = false

-- OR
_||_ : Bool → Bool → Bool
_||_ true y  = true
_||_ false y = y

-- EXERCISE: Implement a function "is-tautology₁?" which checks whether
-- a given input function is constantly true.
is-tautology₁ : (Bool → Bool) → Bool
is-tautology₁ f = (f true) && (f false)

-- EXERCISE: Implement a function "is-tautology₂?" which checks whether
-- a given input function of two arguments is constantly true.
is-tautology₂ : (Bool → Bool → Bool) → Bool
is-tautology₂ f = (((f true true) && (f true false)) && (f false true)) && (f false false)


