module exam.ex4 where

open import types.natural-numbers
open import types.empty
open import types.lists
open import types.equality
open import types.even-odd

-- EXERCISE: Verify some properties about +
lemma-+-zero : (a : ℕ) → (a + zero) ≡ a
lemma-+-zero a = {!!}

lemma-+-succ : (a b : ℕ) → (a + succ b) ≡ succ (a + b)
lemma-+-succ a = {!!}

lemma-+-commutative : (a b : ℕ) → (a + b) ≡ (b + a)
lemma-+-commutative a b = {!!}

lemma-+-associative : (a b c : ℕ) → (a + (b + c)) ≡ ((a + b) + c)
lemma-+-associative a b c = {!!}

lemma-·-distributive : (a b c : ℕ) → ((a + b) · c) ≡ ((a · c) + (b · c))
lemma-·-distributive a b c = {!!}

lemma-succ-pred : ((a : ℕ) → succ (pred a) ≡ a) → ⊥
lemma-succ-pred f = {!!}


-- EXERCISE: Verify some properties about ·
lemma-+-swap : (a b c : ℕ) → (a + (b + c)) ≡ (b + (a + c))
lemma-+-swap a b c = {!!}

lemma-+-swap' : (a b c : ℕ) → (a + (b + c)) ≡ (b + (a + c))
lemma-+-swap' a b c = {!!}

lemma-·-associative : (a b c : ℕ) → ((a · (b · c)) ≡ ((a · b) · c))
lemma-·-associative a b c = {!!}

lemma-·-zero : (a : ℕ) → ((a · zero) ≡ zero)
lemma-·-zero a = {!!}

lemma-·-succ : (a b : ℕ) → ((a · succ b) ≡ (a + (a · b)))
lemma-·-succ a b = {!!}

lemma-·-commutative : (a b : ℕ) → ((a · b) ≡ (b · a))
lemma-·-commutative a b = {!!}


-- EXERCISE: Show that the double of any number is even
lemma-double-even : (a : ℕ) → Even (a + a)
lemma-double-even a = {!!}
