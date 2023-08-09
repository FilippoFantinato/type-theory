module exam-exercises.ex4 where

open import types.natural-numbers
open import types.empty
open import types.lists
open import types.equality


data Bool : Set where
  true  : Bool
  false : Bool

!_ : Bool → Bool
! true = false
! false = true

-- EXERCISE: Show that the two functions "even?" and "even?'" have the same values.
even? : ℕ → Bool
even? zero     = true
even? (succ n) = ! (even? n)

even?' : ℕ → Bool
even?' zero            = true
even?' (succ zero)     = false
even?' (succ (succ n)) = even?' n

lemma-double-negation : (a : Bool) → ! (! a) ≡ a
lemma-double-negation true = refl true
lemma-double-negation false = refl false

lemma-!even?'-even?'-succ : (a : ℕ) → (! even?' a) ≡ (even?' (succ a))
lemma-!even?'-even?'-succ zero = refl false
lemma-!even?'-even?'-succ (succ a) = begin
  ! even?' (succ a) ≡⟨ cong !_ (symm (lemma-!even?'-even?'-succ a)) ⟩
  ! (! even?' a) ≡⟨ lemma-double-negation (even?' a) ⟩
  even?' a ∎

lemma-even?-even?' : (a : ℕ) → even? a ≡ even?' a
lemma-even?-even?' zero = refl true
lemma-even?-even?' (succ a) = begin
  even? (succ a) ≡⟨⟩
  ! (even? a) ≡⟨ cong (!_) (lemma-even?-even?' a) ⟩
  ! (even?' a) ≡⟨ lemma-!even?'-even?'-succ a ⟩
  even?' (succ a) ∎

-- EXERCISE: Show that the predecessor of the successor of a number is that number again.
lemma-pred-succ : (a : ℕ) → pred (succ a) ≡ a
lemma-pred-succ zero = refl zero
lemma-pred-succ (succ a) = refl (succ a)

-- EXERCISE: Show that it is not the case that "succ (pred a) ≡ a" for all natural numbers a.
lemma-1-≠-0 : (succ zero ≡ zero) → ⊥
lemma-1-≠-0 ()

lemma-succ-pred : ((a : ℕ) → succ (pred a) ≡ a) → ⊥
lemma-succ-pred f = lemma-1-≠-0 (f zero)

-- The following defines a type family "Positive : ℕ → Set" such that "Positive a" is the
-- type of witnesses that a is positive: The type "Positive zero" is empty
-- and the types "Positive (succ n)" are inhabited for every n.
data Positive : ℕ → Set where
  -- on purpose, we do NOT include this constructor: zero-is-positive : Positive zero
  succs-are-positive : {n : ℕ} → Positive (succ n)

-- EXERCISE: Fill in this hole.
lemma-succ-pred' : (a : ℕ) → Positive a → succ (pred a) ≡ a
lemma-succ-pred' (succ b) p = refl (succ b)


-- EXERCISE: Verify some properties about +
lemma-+-zero : (a : ℕ) → (a + zero) ≡ a
lemma-+-zero zero = refl zero
lemma-+-zero (succ a) = cong succ (lemma-+-zero a)

lemma-+-succ : (a b : ℕ) → (a + succ b) ≡ succ (a + b)
lemma-+-succ zero b = refl (succ b)
lemma-+-succ (succ a) b = cong succ (lemma-+-succ a b)

lemma-same-succ : {a b : ℕ} → (a ≡ b) → (succ a) ≡ (succ b)
lemma-same-succ q = cong succ q

lemma-+-commutative : (a b : ℕ) → (a + b) ≡ (b + a)
lemma-+-commutative a zero     = lemma-+-zero a
lemma-+-commutative a (succ b) = trans
                                   (lemma-+-succ a b)
                                   (lemma-same-succ (lemma-+-commutative a b))

lemma-+-associative : (a b c : ℕ) → (a + (b + c)) ≡ ((a + b) + c)
lemma-+-associative zero b c = refl (b + c)
lemma-+-associative (succ a) b c = cong succ (lemma-+-associative a b c)

lemma-+-swap : (a b c : ℕ) → (a + (b + c)) ≡ (b + (a + c))
lemma-+-swap zero b c = refl (b + c)
lemma-+-swap (succ a) b c = trans
                              (lemma-same-succ (lemma-+-swap a b c))
                              (symm (lemma-+-succ b (a + c)))


-- EXERCISE: Verify some properties about ·
lemma-·-zero : (a : ℕ) → (a · zero) ≡ zero
lemma-·-zero zero = refl zero
lemma-·-zero (succ a) = lemma-·-zero a

lemma-·-succ : (a b : ℕ) → (a · succ b) ≡ (a + (a · b))
lemma-·-succ zero b = refl zero
lemma-·-succ (succ a) b = begin
  (succ a · succ b) ≡⟨⟩
  succ b + a · succ b ≡⟨ cong (_+_ (succ b)) (lemma-·-succ a b) ⟩
  succ (b + (a + a · b)) ≡⟨ cong succ (lemma-+-swap b a (a · b)) ⟩
  succ (a + (b + a · b)) ∎

lemma-·-distributive : (a b c : ℕ) → ((a + b) · c) ≡ ((a · c) + (b · c))
lemma-·-distributive zero b c = refl (b · c)
lemma-·-distributive (succ a) b c = begin
  succ (a + b) · c ≡⟨⟩
  c + (a + b) · c ≡⟨ cong (_+_ c) (lemma-·-distributive a b c) ⟩
  (c + (a · c + b · c)) ≡⟨ lemma-+-associative c (a · c) (b · c) ⟩
  (c + a · c) + b · c ∎

lemma-·-associative : (a b c : ℕ) → ((a · (b · c)) ≡ ((a · b) · c))
lemma-·-associative zero b c = refl zero
lemma-·-associative (succ a) b c = begin
  (succ a · (b · c)) ≡⟨⟩
  b · c + a · (b · c) ≡⟨ cong (λ z → b · c + z) (lemma-·-associative a b c) ⟩
  b · c + (a · b) · c ≡⟨ symm (lemma-·-distributive b (a · b) c) ⟩
  (b + (a · b)) · c ∎

lemma-·-commutative : (a b : ℕ) → (a · b) ≡ (b · a)
lemma-·-commutative zero b = symm (lemma-·-zero b)
lemma-·-commutative (succ a) b = begin
  succ a · b ≡⟨⟩
  b + (a · b) ≡⟨ cong (_+_ b) (lemma-·-commutative a b) ⟩
  b + (b · a) ≡⟨ symm (lemma-·-succ b a) ⟩
  b · succ a ∎
