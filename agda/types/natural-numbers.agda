module types.natural-numbers where

open import types.booleans

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ


infix 6 _+_ _-_
infix 7 _·_


pred : ℕ → ℕ
pred zero     = zero
pred (succ k) = k


-- EXERCISE: Define the function "half" which divides its input by two.
half : ℕ → ℕ
half zero = zero
half (succ zero) = zero
half (succ (succ x)) = succ (half x)


-- EXERCISE: Define sum.
_+_ : ℕ → ℕ → ℕ
zero + y = y
(succ x) + y = succ (x + y)


_+'_ : ℕ → ℕ → ℕ
x +' zero = x
x +' (succ y) = succ (x + y)


-- EXERCISE: Define (cut-off) subtraction.
_-_ : ℕ → ℕ → ℕ
x - zero   = x
x - succ y = pred (x - y)


-- EXERCISE: Define multiplication
_·_ : ℕ → ℕ → ℕ
zero · y = zero
(succ x) · y = y + (x · y)


-- EXERCISE: Define substraction
_^_ : ℕ → ℕ → ℕ
x ^ zero = succ zero
x ^ (succ y) = (x ^ y) · x


-- EXERCISE: Define a function "eq?" which determines whether its two
-- input numbers are equal.
eq? : ℕ → ℕ → Bool
eq? zero zero         = true
eq? zero (succ y)     = false
eq? (succ x) zero     = false
eq? (succ x) (succ y) = eq? x y


-- EXERCISE: Define a function "≤?" which determines whether its first
-- argument is less than or equal to its second.
_≤_ : ℕ → ℕ → Bool
zero ≤ y = true
(succ x) ≤ zero = false
(succ x) ≤ (succ y) = x ≤ y


-- EXERCISE: Define a function "even?" which determines whether its input is even.
-- even? : ℕ → Bool
-- even? zero = true
-- even? (succ n) = ! (even? n)
