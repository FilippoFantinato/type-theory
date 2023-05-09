module types.even-odd where

open import types.natural-numbers
open import types.sum
open import types.decidable
open import types.empty
open import types.lists


data Even : ℕ → Set where
  base-even : Even zero
  step-even : {n : ℕ} → Even n → Even (succ (succ n))

-- Odd n is the type of witnesses that n is odd
data Odd : ℕ → Set where
  base-odd : Odd (succ zero)
  step-odd : {n : ℕ} → Odd n → Odd (succ (succ n))


lemma-succ-even : {a : ℕ} → Even a → Odd (succ a)
lemma-succ-even base-even = base-odd
lemma-succ-even (step-even a) =  step-odd (lemma-succ-even a)


lemma-succ-odd : {a : ℕ} → Odd a → Even (succ a)
lemma-succ-odd base-odd =  step-even base-even
lemma-succ-odd (step-odd a) =  step-even (lemma-succ-odd a)


lemma-even-odd : (a : ℕ) → (Even a) ⊎ (Odd a)
lemma-even-odd zero = left base-even
lemma-even-odd (succ n) with lemma-even-odd n
... | left x = right (lemma-succ-even x)
... | right x = left (lemma-succ-odd x)


lemma-odd-and-even : {a : ℕ} → Odd a → Even a → ⊥
lemma-odd-and-even (step-odd q) (step-even p) = (lemma-odd-and-even q p)


even? : (n : ℕ) → Dec (Even n)
even? n with lemma-even-odd n
... | left p  = yes p
... | right q = no (lemma-odd-and-even q)

