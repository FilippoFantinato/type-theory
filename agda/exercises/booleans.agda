module exercises.booleans where

open import types.booleans
open import types.sum
open import types.empty


-- EXERCISE: Implement a function "is-tautology₁?" which checks whether
-- a given input function is constantly true.
is-tautology₁ : (Bool → Bool) → Bool
is-tautology₁ f = (f true) && (f false)

-- EXERCISE: Implement a function "is-tautology₂?" which checks whether
-- a given input function of two arguments is constantly true.
is-tautology₂ : (Bool → Bool → Bool) → Bool
is-tautology₂ f = (((f true true) && (f true false)) && (f false true)) && (f false false)

