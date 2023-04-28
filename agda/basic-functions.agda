{- BOOLEANS -}

data Bool : Set where
  true  : Bool
  false : Bool

!_ : Bool → Bool
! true = false
! false = true

_&&_ : Bool → Bool → Bool
_&&_ true y = y
_&&_ false y = false

-- EXERCISE: Implement boolean "or".
-- "false || true" should evaluate to "true".
-- "true  || true" should evaluate to "true".
_||_ : Bool → Bool → Bool
_||_ true y  = true
_||_ false y = y

-- EXERCISE: Implement a function "is-tautology₁?" which checks whether
-- a given input function is constantly true.
is-tautology₁ : (Bool → Bool) → Bool
is-tautology₁ f = (f true) && (f false)

-- EXERCISE: Implement a function "is-tautology₂?" which checks whether
-- a given input function of two arguments is constantly true.
is-tautology₂ : (Bool → Bool → Bool) → Bool
is-tautology₂ f = (((f true true) && (f true false)) && (f false true)) && (f false false)

{- NATURAL NUMBERS -}

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

pred : ℕ → ℕ
pred zero     = zero
pred (succ k) = k

-- EXERCISE: Define the function "half" which divides its input by two.
half : ℕ → ℕ
half zero = zero
half (succ zero) = zero
half (succ (succ n)) = succ (half n)

-- EXERCISE: Define sum.
_+_ : ℕ → ℕ → ℕ
zero + y = y
x + zero = x
x + (succ y) = (succ x) + y

-- EXERCISE: Define (cut-off) subtraction.
_-_ : ℕ → ℕ → ℕ
zero - y = zero
x - zero = x
(succ x) - (succ y) = x - y

-- EXERCISE: Define multiplication
_*_ : ℕ → ℕ → ℕ
zero * y = zero
(succ x) * zero = zero
x * (succ zero) = x
x * (succ y) = (x * y) + x

-- EXERCISE: Define substraction
_^_ : ℕ → ℕ → ℕ
zero ^ y = zero
x ^ zero = succ zero
x ^ (succ zero) = x
x ^ (succ y) = (x ^ y) * x

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
even? (succ n) = ! (even? n)

{- WEIRD TYPE -}

-- EXERCISE: Describe the following type in simple terms. What are its values?
data Weird : Set where
  foo : Weird → Weird

{- The terms of the Weird type are the functions from itself and to itself -}
