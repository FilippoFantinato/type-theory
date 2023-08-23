module exam-exercises-2.ex4 where

open import types.natural-numbers
open import types.empty
open import types.lists
open import types.equality


data Bool : Set where


!_ : Bool → Bool
! a = {!!}

-- EXERCISE: Show that the two functions "even?" and "even?'" have the same values.
even? : ℕ → Bool
even? a = {!!}

even?' : ℕ → Bool
even?' a = {!!}

lemma-double-negation : (a : Bool) → ! (! a) ≡ a
lemma-double-negation a = {!!}

lemma-!even?'-even?'-succ : (a : ℕ) → (! even?' a) ≡ (even?' (succ a))
lemma-!even?'-even?'-succ a = {!!}

lemma-even?-even?' : (a : ℕ) → even? a ≡ even?' a
lemma-even?-even?' a = {!!}

-- EXERCISE: Show that the predecessor of the successor of a number is that number again.
lemma-pred-succ : (a : ℕ) → pred (succ a) ≡ a
lemma-pred-succ a = {!!}

-- EXERCISE: Show that it is not the case that "succ (pred a) ≡ a" for all natural numbers a.
lemma-1-≠-0 : (succ zero ≡ zero) → ⊥
lemma-1-≠-0 a = {!!}

lemma-succ-pred : ((a : ℕ) → succ (pred a) ≡ a) → ⊥
lemma-succ-pred f = {!!}

-- The following defines a type family "Positive : ℕ → Set" such that "Positive a" is the
-- type of witnesses that a is positive: The type "Positive zero" is empty
-- and the types "Positive (succ n)" are inhabited for every n.
data Positive : ℕ → Set where
  -- on purpose, we do NOT include this constructor: zero-is-positive : Positive zero

-- EXERCISE: Fill in this hole.
lemma-succ-pred' : (a : ℕ) → Positive a → succ (pred a) ≡ a
lemma-succ-pred' a = {!!}


-- EXERCISE: Verify some properties about +
lemma-+-zero : (a : ℕ) → (a + zero) ≡ a
lemma-+-zero a = {!!}

lemma-+-succ : (a b : ℕ) → (a + succ b) ≡ succ (a + b)
lemma-+-succ a = {!!}

lemma-same-succ : {a b : ℕ} → (a ≡ b) → (succ a) ≡ (succ b)
lemma-same-succ a = {!!}

lemma-+-commutative : (a b : ℕ) → (a + b) ≡ (b + a)
lemma-+-commutative a b = {!!}

lemma-+-associative : (a b c : ℕ) → (a + (b + c)) ≡ ((a + b) + c)
lemma-+-associative a b c = {!!}

lemma-+-swap : (a b c : ℕ) → (a + (b + c)) ≡ (b + (a + c))
lemma-+-swap a b c = {!!}


-- EXERCISE: Verify some properties about ·
lemma-·-zero : (a : ℕ) → (a · zero) ≡ zero
lemma-·-zero a = {!!}

lemma-·-succ : (a b : ℕ) → (a · succ b) ≡ (a + (a · b))
lemma-·-succ a b = {!!}

lemma-·-distributive : (a b c : ℕ) → ((a + b) · c) ≡ ((a · c) + (b · c))
lemma-·-distributive a b c = {!!}

lemma-·-associative : (a b c : ℕ) → ((a · (b · c)) ≡ ((a · b) · c))
lemma-·-associative a b c = {!!}

lemma-·-commutative : (a b : ℕ) → (a · b) ≡ (b · a)
lemma-·-commutative a b = {!!}
