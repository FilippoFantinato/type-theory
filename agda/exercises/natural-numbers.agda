{-# OPTIONS --allow-unsolved-metas #-}

module exercises.natural-numbers where

open import types.equality
open import types.natural-numbers
open import types.empty
open import types.positive

----------------------
------ IDENTITY ------
----------------------

-- zero ≡ zero is the type of witnesses that zero equals zero
-- zero ≡ succ zero is the type of witnesses that zero equals succ zero (this must be empty)
lemma-zero-identity : zero ≡ zero
lemma-zero-identity = refl zero

---------------------------
--------- SUM -------------
---------------------------

lemma-zero-+ : (b : ℕ) → ((zero + b) ≡ b)
lemma-zero-+ b = refl b

lemma-+-zero : (a : ℕ) → ((a + zero) ≡ a)
lemma-+-zero zero = lemma-zero-identity
lemma-+-zero (succ a) = cong succ (lemma-+-zero a)

lemma-+-same-succ : {a b : ℕ} → a ≡ b → (succ a) ≡ (succ b)
lemma-+-same-succ el = cong succ el

lemma-+-succ : (a b : ℕ) → ((a + (succ b)) ≡ succ (a + b))
lemma-+-succ zero b     = refl (succ b)
lemma-+-succ (succ a) b = cong succ (lemma-+-succ a b)

lemma-+-commutative : (a b : ℕ) → ((b + a) ≡ (a + b))
lemma-+-commutative zero b = lemma-+-zero b
lemma-+-commutative (succ a) b = trans (lemma-+-succ b a) (cong succ (lemma-+-commutative a b))

lemma-same-sum : (x y : ℕ) → (x + y) ≡ (x +' y)
lemma-same-sum x zero = lemma-+-zero x
lemma-same-sum x (succ y) = lemma-+-succ x y

-- EXERCISE: Verify that addition is associative.
lemma-+-associative : (a b c : ℕ) → (a + (b + c)) ≡ ((a + b) + c)
lemma-+-associative zero b c = refl (b + c)
lemma-+-associative (succ a) b c = cong succ (lemma-+-associative a b c)


---------------------------
------ MULTIPLICATION -----
---------------------------

lemma-·-distributive : (a b c : ℕ) → ((a + b) · c) ≡ ((a · c) + (b · c))
lemma-·-distributive zero b c = refl (b · c)
lemma-·-distributive (succ a) b c = begin
  ((succ a + b) · c)        ≡⟨⟩  -- by definition
  (succ (a + b) · c)        ≡⟨⟩  -- by definition
  c + ((a + b) · c)         ≡⟨ cong (_+_ c) (lemma-·-distributive a b c) ⟩
  c + ((a · c) + (b · c))   ≡⟨ lemma-+-associative c (a · c) (b · c) ⟩
  (c + (a · c)) + (b · c)   ≡⟨⟩
  (succ a · c) + (b · c)    ∎

lemma-·-associative : (a b c : ℕ) → a · (b · c) ≡ (a · b) · c
lemma-·-associative zero b c = refl zero
lemma-·-associative (succ a) b c = begin
  (succ a) · (b · c) ≡⟨⟩
  (b · c) + a · (b · c) ≡⟨ cong (λ z → b · c + z) (lemma-·-associative a b c) ⟩
  (b · c) + (a · b) · c ≡⟨ symm (lemma-·-distributive b (a · b) c) ⟩
  (b + a · b) · c       ≡⟨⟩
  (succ a · b) · c      ∎

-- cong (λ z → b · c + z) (lemma-·-associative a b c)

 --  {!(b · c) + (a · b) · c ≡⟨ symm  ? ⟩ !}
 --  {!(b + a · b) · c 
  -- (b · c) + a · (b · c) 
  -- (b · c) + ((a · b) · c) ≡⟨⟩
  -- ?

---------------------------
-------- SUCC PRED --------
---------------------------

-- EXERCISE: Show that it is not the case that "succ (pred a) ≡ a" for all natural numbers a.
lemma-succ-pred : ((a : ℕ) → succ (pred a) ≡ a) → ⊥
lemma-succ-pred f with (f zero)
... | ()

-- EXERCISE: Fill in this hole.
lemma-succ-pred' : (a : ℕ) → Positive a → succ (pred a) ≡ a
lemma-succ-pred' (succ a) p = refl _
