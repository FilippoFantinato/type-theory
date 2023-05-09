module types.trees where

open import types.empty
open import types.natural-numbers

data BinaryTree (A : Set) : Set where
  nil : BinaryTree A
  fork : A → BinaryTree A → BinaryTree A → BinaryTree A


exampleBinaryTree : {A : Set} → A → A → A → BinaryTree A
exampleBinaryTree x y a = fork x nil (fork y (fork a nil nil)  nil)


-- zero : ℕ : Set : Set₁ : Set₂ : Set₃ : ... : Setω : ...

data V : Set₁ where
  sup : {I : Set} → (I → V) → V

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
