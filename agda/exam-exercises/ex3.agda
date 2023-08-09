{-# OPTIONS --allow-unsolved-metas #-}

module exam-exercises.ex3 where

open import types.natural-numbers
open import types.booleans
open import types.sum

data ⊥ : Set where


¬_ : Set → Set
¬ X = X → ⊥

infix 5 _≡_

-- Define equality
data _≡_ {X : Set} : X → X → Set where
  refl : (x : X) → x ≡ x

infix  1 begin_
infixr 2 _≡⟨⟩_ _≡⟨_⟩_
infix  3 _∎

-- Define some generalities on equality
-- EXERCISE: Fill in this hole, thereby proving that equality is a "congruence";
-- by this lemma, we can apply the same operation to the two sides of an equation
-- and still be sure that the equation holds.
cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f (refl x) = refl (f x)

symm : {A : Set} {x y : A} → x ≡ y → y ≡ x
symm (refl x) = refl x

-- EXERCISE: Fill in this hole, thereby proving that equality is transitive.
trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans (refl _) p = p

-- EXERCISE: Prove that equal functions have equal values. (The
-- converse is a principle known as "function extensionality" which
-- can be postulated in Agda but is not assumed by default.)
equal→pwequal : {A B : Set} {f g : A → B} → (x : A) → f ≡ g → f x ≡ g x
equal→pwequal x (refl f) = refl (f x)

-- EXERCISE: Think about the expression "(⊥ ≡ ℕ)". Is it well-defined?
-- What would be its meaning?

-- EXERCISE: Fill in this hole. This lemma will be used below
-- in the proof that the double of any number is even.
transport : {A : Set} {x y : A} → (F : A → Set) → x ≡ y → F x → F y
transport F (refl p) s = s



begin_ : {A : Set} {x y : A} → x ≡ y → x ≡ y
begin p = p

_≡⟨_⟩_ : {A : Set} {y z : A} → (x : A) → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ p ⟩ q = trans p q

_≡⟨⟩_ : {A : Set} {y : A} → (x : A) → (q : x ≡ y) → x ≡ y
x ≡⟨⟩ q = q

_∎ : {A : Set} → (x : A) → x ≡ x
x ∎ = refl x

-- Define some logical tautologies

dni : {A B : Set} → A → ¬ (¬ A)
dni p u = u p

contraposition : {A B : Set} → (A → B) → (¬ B → ¬ A)
contraposition f p a = p (f a)

de-morgan₁ : {A B : Set} → ¬ (A ⊎ B) → ¬ A
de-morgan₁ p a = p (left a)

de-morgan₂ : {A B : Set} → ¬ (A ⊎ B) → ¬ B
de-morgan₂ p b = p (right b)


-- Equalities of numbers

-- EXERCISE: Show that the predecessor of the successor of a number is that number again.
lemma-pred-succ : (a : ℕ) → pred (succ a) ≡ a
lemma-pred-succ zero = refl zero
lemma-pred-succ (succ a) = refl (succ a)

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

-- EXERCISE: Verify the following two auxiliary lemmas, establishing that we
-- could have equivalently defined addition also by recursion on the second argument.
lemma-+-zero : (a : ℕ) → (a + zero) ≡ a
lemma-+-zero zero = refl zero
lemma-+-zero (succ a) = cong succ (lemma-+-zero a)

lemma-+-succ : (a b : ℕ) → (a + succ b) ≡ succ (a + b)
lemma-+-succ zero b = refl (succ b)
lemma-+-succ (succ a) b = cong succ (lemma-+-succ a b)

lemma-same-succ : {a b : ℕ} → (a ≡ b) → (succ a) ≡ (succ b)
lemma-same-succ q = cong succ q

-- EXERCISE: Verify that addition is commutative.
lemma-+-commutative : (a b : ℕ) → (a + b) ≡ (b + a)
lemma-+-commutative a zero     = lemma-+-zero a
lemma-+-commutative a (succ b) = trans
                                   (lemma-+-succ a b)
                                   (lemma-same-succ (lemma-+-commutative a b))

-- EXERCISE: Verify that addition is associative.
lemma-+-associative : (a b c : ℕ) → (a + (b + c)) ≡ ((a + b) + c)
lemma-+-associative zero b c = refl (b + c)
lemma-+-associative (succ a) b c = cong succ (lemma-+-associative a b c)

-- EXERCISE: Fill in this hole
lemma-+-swap : (a b c : ℕ) → (a + (b + c)) ≡ (b + (a + c))
lemma-+-swap zero b c = refl (b + c)
lemma-+-swap (succ a) b c = trans
                              (lemma-same-succ (lemma-+-swap a b c))
                              (symm (lemma-+-succ b (a + c)))

-- EXERCISE: Fill in this hole.
lemma-·-zero : (a : ℕ) → (a · zero) ≡ zero
lemma-·-zero zero = refl zero
lemma-·-zero (succ a) = lemma-·-zero a

-- EXERCISE: Fill in this hole.
lemma-·-succ : (a b : ℕ) → (a · succ b) ≡ (a + (a · b))
lemma-·-succ zero b = refl zero
lemma-·-succ (succ a) b = begin
  (succ a · succ b) ≡⟨⟩
  succ b + a · succ b ≡⟨ cong (_+_ (succ b)) (lemma-·-succ a b) ⟩
  succ (b + (a + a · b)) ≡⟨ cong succ (lemma-+-swap b a (a · b)) ⟩
  succ (a + (b + a · b)) ∎

-- EXERCISE: Verify the distributive law. Similar as the implementation/proof
-- of lemma-+-commutative, the result will not be easy to read.
-- By a technique called "equational reasoning", to be introduced next week,
-- we will be able to clean up the proof.
lemma-·-distributive : (a b c : ℕ) → ((a + b) · c) ≡ ((a · c) + (b · c))
lemma-·-distributive zero b c = refl (b · c)
lemma-·-distributive (succ a) b c = begin
  succ (a + b) · c ≡⟨⟩
  c + (a + b) · c ≡⟨ cong (_+_ c) (lemma-·-distributive a b c) ⟩
  (c + (a · c + b · c)) ≡⟨ lemma-+-associative c (a · c) (b · c) ⟩
  (c + a · c) + b · c ∎

-- EXERCISE: Verify associativity of multiplication
lemma-·-associative : (a b c : ℕ) → ((a · (b · c)) ≡ ((a · b) · c))
lemma-·-associative zero b c = refl zero
lemma-·-associative (succ a) b c = begin
  (succ a · (b · c)) ≡⟨⟩
  b · c + a · (b · c) ≡⟨ cong (λ z → b · c + z) (lemma-·-associative a b c) ⟩
  b · c + (a · b) · c ≡⟨ symm (lemma-·-distributive b (a · b) c) ⟩
  (b + (a · b)) · c ∎

-- EXERCISE: Verify the commutativity of multiplication
lemma-·-commutative : (a b : ℕ) → (a · b) ≡ (b · a)
lemma-·-commutative zero b = symm (lemma-·-zero b)
lemma-·-commutative (succ a) b = begin
  succ a · b ≡⟨⟩
  b + (a · b) ≡⟨ cong (_+_ b) (lemma-·-commutative a b) ⟩
  b + (b · a) ≡⟨ symm (lemma-·-succ b a) ⟩
  b · succ a ∎
