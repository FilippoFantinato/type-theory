module natural-numbers where

open import booleans


data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ


pred : ℕ → ℕ
pred zero     = zero
pred (succ k) = k


-- EXERCISE: Define the function "half" which divides its input by two.
half : ℕ → ℕ
half zero = zero
half (succ x) = succ (half x)


-- EXERCISE: Define sum.
_+_ : ℕ → ℕ → ℕ
zero + y = y
(succ x) + y = succ (x + y)

-- EXERCISE: Define (cut-off) subtraction.
_-_ : ℕ → ℕ → ℕ
zero - y = zero
(succ x) - y = succ (x - y)


-- EXERCISE: Define multiplication
_·_ : ℕ → ℕ → ℕ
zero · y = zero
(succ x) · y = x + (x · y)

-- EXERCISE: Define substraction
_^_ : ℕ → ℕ → ℕ
x ^ zero = succ zero
x ^ (succ y) = (x ^ y) · x


-- EXERCISE: Define a function "eq?" which determines whether its two
-- input numbers are equal.
eq? : ℕ → ℕ → Bool
eq? zero zero = true
eq? x zero = false
eq? zero y = false
eq? (succ x) (succ y) = eq? x y

-- EXERCISE: Define a function "≤?" which determines whether its first
-- argument is less than or equal to its second.
_≦_ : ℕ → ℕ → Bool
zero ≦ y = true
x ≦ zero = false
(succ x) ≦ (succ y) = x ≦ y

-- EXERCISE: Define a function "even?" which determines whether its input is even.
even? : ℕ → Bool
even? zero = true
even? (succ zero) = false
even? (succ n) = ¬ (even? n)
