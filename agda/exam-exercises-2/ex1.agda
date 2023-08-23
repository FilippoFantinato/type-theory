module exam-exercises-2.ex1 where

open import types.equality

-- Define Boolean type
data Bool : Set where

-- Define Natural numbers type
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ


-- Define boolean operations
_||_ : Bool → Bool → Bool
a || b = {!!}

_&&_ : Bool → Bool → Bool
a && b = {!!}

!_ : Bool → Bool
! a = {!!}


-- Define some natural number operations
half : ℕ → ℕ
half a = {!!}

_+_ : ℕ → ℕ → ℕ
a + b = {!!}

pred : ℕ → ℕ
pred a = {!!}

_-_ : ℕ → ℕ → ℕ
a - b = b

_·_ : ℕ → ℕ → ℕ
a · b = {!!}

eq? : ℕ → ℕ → Bool
eq? a b = {!!}

≤? : ℕ → ℕ → Bool
≤? a b = {!!}

even? : ℕ → Bool
even? a = {!!}


-- Define Even witness
data Even : ℕ → Set where


-- Define Odd witness
data Odd : ℕ → Set where

-- Define some lemmas about even and odd numbers
lemma-sum-even : {a b : ℕ} → Even a → Even b → Even (a + b)
lemma-sum-even a b = {!!}

lemma-succ-even : {a : ℕ} → Even a → Odd (succ a)
lemma-succ-even a = {!!}

lemma-succ-odd : {a : ℕ} → Odd a → Even (succ a)
lemma-succ-odd a = {!!}

lemma-sum-odd : {a b : ℕ} → Odd a → Odd b → Even (a + b)
lemma-sum-odd a b = {!!}

lemma-sum-mixed : {a b : ℕ} → Even a → Odd b → Odd (a + b)
lemma-sum-mixed a b = {!!}

lemma-+-succ : (a b : ℕ) → ((succ a + b) ≡ (succ (a + b)))
lemma-+-succ a b = {!!}

lemma-double-even : (a : ℕ) → Even (a + a)
lemma-double-even a = {!!}


-- Define Sum type
data _⊎_ (A B : Set) : Set where

-- Every natural number is either even or odd
lemma-even-odd : (a : ℕ) → (Even a ⊎ Odd a)
lemma-even-odd a = {!!}
