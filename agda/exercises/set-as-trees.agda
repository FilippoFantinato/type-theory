module exercises.set-as-trees where

open import types.V
open import types.empty
open import types.natural-numbers

-- In predicative mathematics, we don't have the powerset operation
-- P({a,b}) = {}

-- GOAL: define an Agda type V of sets accompanied by functions as
-- emptySet : V        ∅
-- pair : V → V → V    pair x y = {x,y}
-- singleton : V → V   singleon x = {x}
-- _⊎_ : V → V → V
-- powerset : V → V    fail by defining it


-- zero : ℕ : Set : Set₁ : Set₂ : Set₃ : ... : Setω : ...

-- Empty set defined via V type
∅ : V
∅ = sup {⊥} empty-function
  where
  empty-function : ⊥ → V
  empty-function ()

-- Pair type defined via V type
pair : V → V → V
pair x y = sup {𝟚} f
  where
  data 𝟚 : Set where
    left  : 𝟚
    right : 𝟚

  f : 𝟚 → V
  f left  = x
  f right = y

-- define a value ℕ : V which deserves the same "set of all natural numbers"
-- succ constructor defiend via V type
next : V → V
next x@(sup {I} f) = sup {J} g
  where
  data J : Set where
    old : I → J
    new : J

  g : J → V
  g (old i) = f i
  g new = x


-- Any natural number defined as in set theory
fromℕ : ℕ → V
fromℕ zero = ∅
fromℕ (succ n) = next (fromℕ n)

-- Set of natural numberd defined via V
ℕ' : V
ℕ' = sup {ℕ} fromℕ
