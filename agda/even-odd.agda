open import natural-numbers
open import empty-type
open import sum-type


-- Even n is the type of witnesses that n is even
data Even : ℕ → Set where
  base-even : Even zero
  step-even : {n : ℕ} → Even n → Even (succ (succ n))

-- Odd n is the type of witnesses that n is odd
data Odd : ℕ → Set where
  base-odd : Odd (succ zero)
  step-odd : {n : ℕ} → Odd n → Odd (succ (succ n))


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

lemma-even-odd : (a : ℕ) → (Even a) ⊎ (Odd a)
lemma-even-odd zero = left base-even
lemma-even-odd (succ n) with lemma-even-odd n
... | left x = right (lemma-succ-even x)
... | right x = left (lemma-succ-odd x)


-- Prove that it's not the case that succeccors of even numbers are even
lemma-succ-even-not-even : ((n : ℕ) → Even n → Even (succ n)) → ⊥
lemma-succ-even-not-even f = lemma-one-not-even (f zero base-even)



lemma-double-even : (a : ℕ) → Even (a + a)
lemma-double-even zero     = base-even
lemma-double-even (succ a) = {!!}
