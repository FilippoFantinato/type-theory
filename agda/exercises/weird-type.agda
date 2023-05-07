module exercises.weird-type where

open import types.empty
open import types.natural-numbers


-- EXERCISE: Describe the following type in simple terms. What are its values?
data Weird : Set where
  foo : Weird → Weird

-- Weird has no terms and the proof of that follows from the following

-- This type is manifestly empty
data Empty : Set where

-- The following hole can not be filled
f : ℕ → Empty
f n = {!   !}

-- There is a function from x to Empty only in the case that x itself is an empty type
g : Empty → Empty
g x = x

-- Isomorphism which proves Weird is emtpy
h : Weird → Empty
h (foo x) =  h x 

