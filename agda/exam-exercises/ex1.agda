module exam-exercises.ex1 where

-- Define Boolean type
data Bool : Set where
  true  : Bool
  false : Bool

-- Define Natural numbers type
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ



-- Define boolean operations
_||_ : Bool → Bool → Bool
a || true = true
a || false = a

_&&_ : Bool → Bool → Bool
a && true = a
a && false = false

_! : Bool → Bool
true ! = false
false ! = true


-- Define some natural number operations
half : ℕ → ℕ
half zero = zero
half (succ zero) = zero
half (succ (succ n)) = succ (half n)

_+_ : ℕ → ℕ → ℕ
a + zero = a
a + succ b = succ (a + b)

pred : ℕ → ℕ
pred zero = zero
pred (succ a) = a

_-_ : ℕ → ℕ → ℕ
a - zero = a
a - succ b = pred (a - b)

_·_ : ℕ → ℕ → ℕ
a · zero = zero
a · succ b = a + (a · b)

div : ℕ → ℕ → ℕ
div zero b = zero
div (succ a) b = b - div a b

eq? : ℕ → ℕ → Bool
eq? zero zero = true
eq? zero (succ b) = false
eq? (succ a) zero = false
eq? (succ a) (succ b) = eq? a b

≤? : ℕ → ℕ → Bool
≤? zero b = true
≤? (succ a) zero = false
≤? (succ a) (succ b) = ≤? a b

even? : ℕ → Bool
even? zero = true
even? (succ n) = (even? n) !


-- Define Even witness
data Even : ℕ → Set where
  base-even : Even zero
  step-even : {n : ℕ} → Even n → Even (succ (succ n))


-- Define Odd witness
data Odd : ℕ → Set where
  base-odd  : Odd (succ zero)
  step-odd : {n : ℕ} → Odd n → Odd (succ (succ n))

-- Define some lemmas about even and odd numbers
lemma-sum-even : {a b : ℕ} → Even a → Even b → Even (a + b)
lemma-sum-even a base-even = a
lemma-sum-even a (step-even b) = step-even (lemma-sum-even a b)

lemma-succ-even : {a : ℕ} → Even a → Odd (succ a)
lemma-succ-even base-even = base-odd
lemma-succ-even (step-even a) = step-odd (lemma-succ-even a)

lemma-succ-odd : {a : ℕ} → Odd a → Even (succ a)
lemma-succ-odd base-odd = step-even base-even
lemma-succ-odd (step-odd a) = step-even (lemma-succ-odd a)

lemma-sum-odd : {a b : ℕ} → Odd a → Odd b → Even (a + b)
lemma-sum-odd a base-odd     = lemma-succ-odd a
lemma-sum-odd a (step-odd b) = step-even (lemma-sum-odd a b)

lemma-sum-mixed : {a b : ℕ} → Even a → Odd b → Odd (a + b)
lemma-sum-mixed a base-odd = lemma-succ-even a
lemma-sum-mixed a (step-odd b) = step-odd (lemma-sum-mixed a b)


-- Define Sum type
data _⊎_ (A B : Set) : Set where
  left  : (n : A) → A ⊎ B
  right : (n : B) → A ⊎ B

-- Every natural number is either even or odd
lemma-even-odd : (a : ℕ) → (Even a ⊎ Odd a)
lemma-even-odd zero = left base-even
lemma-even-odd (succ a) with lemma-even-odd a
... | left n = right (lemma-succ-even n)
... | right n = left (lemma-succ-odd n)
