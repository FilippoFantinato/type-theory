module exercises.even-odd where

open import types.natural-numbers
open import types.empty
open import types.sum
open import types.equality
open import types.even-odd

open import exercises.natural-numbers

lemma-sum-even : {a b : ℕ} → Even a → Even b → Even (a + b)
lemma-sum-even base-even b = b
lemma-sum-even (step-even a) b = step-even (lemma-sum-even a b)


lemma-succ-even : {a : ℕ} → Even a → Odd (succ a)
lemma-succ-even base-even = base-odd
lemma-succ-even (step-even a) =  step-odd (lemma-succ-even a)


lemma-succ-odd : {a : ℕ} → Odd a → Even (succ a)
lemma-succ-odd base-odd =  step-even base-even
lemma-succ-odd (step-odd a) =  step-even (lemma-succ-odd a)


lemma-sum-odd : {a b : ℕ} → Odd a → Odd b → Even (a + b)
lemma-sum-odd base-odd base-odd = step-even base-even
lemma-sum-odd base-odd b = lemma-succ-odd b
lemma-sum-odd (step-odd a) b = step-even (lemma-sum-odd a b)


lemma-sum-mixed : {a b : ℕ} → Even a → Odd b → Odd (a + b)
lemma-sum-mixed base-even base-odd =  base-odd
lemma-sum-mixed base-even b = b
lemma-sum-mixed (step-even a) b = step-odd (lemma-sum-mixed a b)


lemma-one-not-even : Even (succ zero) → ⊥
lemma-one-not-even ()

-- Prove that it's not the case that succeccors of even numbers are even
lemma-succ-even-not-even : ((n : ℕ) → Even n → Even (succ n)) → ⊥
lemma-succ-even-not-even f = lemma-one-not-even (f zero base-even)

{-
lemma-double-even : (a : ℕ) → Even (a + a)
lemma-double-even zero     = base-even
lemma-double-even (succ a) = transport Even e' p
  where
  p : Even (succ (succ (a + a)))
  p = step-even (lemma-double-even a)

  e : (succ (a + a)) ≡ (a + (succ a))
  e = symm (lemma-+-succ a a)

  e' : succ (succ (a + a)) ≡ succ (a + (succ a))
  e' = cong succ e
-}

{-
lemma-double-even : (a : ℕ) → Even (a + a)
lemma-double-even zero = base-even
lemma-double-even (succ a) = transport Even (cong succ (symm (lemma-+-succ a a)))
-}

lemma-double-even : (a : ℕ) → Even (a + a)
lemma-double-even zero = base-even
lemma-double-even (succ b) rewrite (lemma-+-succ b b) = step-even (lemma-double-even b)



-- EXERCISE: Complete a well-known logical tautology
contrapposition : {A B R : Set} → (A → B) → ((B → R) → (A → R))
contrapposition f = (λ z z₁ → z (f z₁))


-- EXERCISE: Verify that disjunction is commutative, in the following sense:
or-commutative : {A B : Set} → (A ⊎ B) → (B ⊎ A)
or-commutative (left x)  =  right x
or-commutative (right x) = left x
