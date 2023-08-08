{-# OPTIONS --allow-unsolved-metas #-}

module exam.ex3 where

open import types.natural-numbers
open import types.booleans
open import types.sum

data ⊥ : Set where


¬_ : Set → Set
¬ X = X → ⊥

infix 5 _≡_

-- Define equality
data _≡_ {X : Set} : X → X → Set where


-- Define some logical tautologies

dni : {A B : Set} → A → ¬ (¬ A)
dni p = {!!}

contraposition : {A B : Set} → (A → B) → (¬ B → ¬ A)
contraposition f p = {!!}

de-morgan₁ : {A B : Set} → ¬ (A ⊎ B) → ¬ A
de-morgan₁ p = {!!}

de-morgan₂ : {A B : Set} → ¬ (A ⊎ B) → ¬ B
de-morgan₂ p = {!!}

-- Define some generalities on equality
-- EXERCISE: Fill in this hole, thereby proving that equality is a "congruence";
-- by this lemma, we can apply the same operation to the two sides of an equation
-- and still be sure that the equation holds.
cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f p = {!!}

symm : {A : Set} {x y : A} → x ≡ y → y ≡ x
symm p = {!!}

-- EXERCISE: Fill in this hole, thereby proving that equality is transitive.
trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans p q = {!!}

-- EXERCISE: Prove that equal functions have equal values. (The
-- converse is a principle known as "function extensionality" which
-- can be postulated in Agda but is not assumed by default.)
equal→pwequal : {A B : Set} {f g : A → B} {x : A} → f ≡ g → f x ≡ g x
equal→pwequal p = {!!}

-- EXERCISE: Think about the expression "(⊥ ≡ ℕ)". Is it well-defined?
-- What would be its meaning?

-- EXERCISE: Fill in this hole. This lemma will be used below
-- in the proof that the double of any number is even.
transport : {A : Set} {x y : A} → (F : A → Set) → x ≡ y → F x → F y
transport F p s = {!!}

-- Equalities of numbers

-- EXERCISE: Show that the predecessor of the successor of a number is that number again.
lemma-pred-succ : (a : ℕ) → pred (succ a) ≡ a
lemma-pred-succ a = {!!}

-- EXERCISE: Show that the two functions "even?" and "even?'" have the same values.
even? : ℕ → Bool
even? zero     = true
even? (succ n) = ! (even? n)

even?' : ℕ → Bool
even?' zero            = true
even?' (succ zero)     = false
even?' (succ (succ n)) = even?' n

lemma-even?-even?' : (a : ℕ) → even? a ≡ even?' a
lemma-even?-even?' a = {!!}

-- EXERCISE: Show that it is not the case that "succ (pred a) ≡ a" for all natural numbers a.
lemma-succ-pred : ((a : ℕ) → succ (pred a) ≡ a) → ⊥
lemma-succ-pred f = {!!}

-- The following defines a type family "Positive : ℕ → Set" such that "Positive a" is the
-- type of witnesses that a is positive: The type "Positive zero" is empty
-- and the types "Positive (succ n)" are inhabited for every n.
data Positive : ℕ → Set where
  -- on purpose, we do NOT include this constructor: zero-is-positive : Positive zero
  succs-are-positive : {n : ℕ} → Positive (succ n)

-- EXERCISE: Fill in this hole.
lemma-succ-pred' : (a : ℕ) → Positive a → succ (pred a) ≡ a
lemma-succ-pred' (succ b) p = {!!}

-- EXERCISE: Verify the following two auxiliary lemmas, establishing that we
-- could have equivalently defined addition also by recursion on the second argument.
lemma-+-zero : (a : ℕ) → (a + zero) ≡ a
lemma-+-zero a = {!!}

lemma-+-succ : (a b : ℕ) → (a + succ b) ≡ succ (a + b)
lemma-+-succ a b = {!!}

-- EXERCISE: Verify that addition is commutative.
lemma-+-commutative : (a b : ℕ) → (a + b) ≡ (b + a)
lemma-+-commutative a b = {!!}

-- EXERCISE: Verify that addition is associative.
lemma-+-associative : (a b c : ℕ) → (a + (b + c)) ≡ ((a + b) + c)
lemma-+-associative a b c = {!!}

-- EXERCISE: Fill in this hole
lemma-+-swap : (a b c : ℕ) → (a + (b + c)) ≡ (b + (a + c))
lemma-+-swap a b c = {!!}

-- EXERCISE: Fill in this hole.
lemma-·-zero : (a : ℕ) → (a · zero) ≡ zero
lemma-·-zero a = {!!}

-- EXERCISE: Fill in this hole.
lemma-·-succ : (a b : ℕ) → (a · succ b) ≡ (a + (a · b))
lemma-·-succ a b = {!!}

-- EXERCISE: Verify the commutativity of multiplication
lemma-·-commutative : (a b : ℕ) → (a · b) ≡ (b · a)
lemma-·-commutative a b = {!!}

-- EXERCISE: Verify associativity of multiplication
lemma-·-associative : (a b c : ℕ) → ((a · (b · c)) ≡ ((a · b) · c))
lemma-·-associative a b c = {!!}

-- EXERCISE: Verify the distributive law. Similar as the implementation/proof
-- of lemma-+-commutative, the result will not be easy to read.
-- By a technique called "equational reasoning", to be introduced next week,
-- we will be able to clean up the proof.
lemma-·-distributive : (a b c : ℕ) → ((a + b) · c) ≡ ((a · c) + (b · c))
lemma-·-distributive a b c = {!!}
