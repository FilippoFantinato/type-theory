{-# OPTIONS --allow-unsolved-metas #-}

module exam-exercises-2.ex3 where

open import types.natural-numbers
open import types.booleans
open import types.sum
open import types.equality

data ⊥ : Set where

¬_ : Set → Set
¬ X = X → ⊥

-- Define equality
{-
data _≡_ {X : Set} : X → X → Set where
-}

-- Define some generalities on equality
-- EXERCISE: Fill in this hole, thereby proving that equality is a "congruence";
-- by this lemma, we can apply the same operation to the two sides of an equation
-- and still be sure that the equation holds.
cong' : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong' f a = {!!}

symm' : {A : Set} {x y : A} → x ≡ y → y ≡ x
symm' a = {!!}

-- EXERCISE: Fill in this hole, thereby proving that equality is transitive.
trans' : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans' a b = {!!}

-- EXERCISE: Prove that equal functions have equal values. (The
-- converse is a principle known as "function extensionality" which
-- can be postulated in Agda but is not assumed by default.)
equal→pwequal' : {A B : Set} {f g : A → B} → (x : A) → f ≡ g → f x ≡ g x
equal→pwequal' a b = {!!}

-- EXERCISE: Think about the expression "(⊥ ≡ ℕ)". Is it well-defined?
-- What would be its meaning?

-- EXERCISE: Fill in this hole. This lemma will be used below
-- in the proof that the double of any number is even.
transport' : {A : Set} {x y : A} → (F : A → Set) → x ≡ y → (F x → F y)
transport' F a = {!!}

-- Define some logical tautologies

dni : {A B : Set} → A → ¬ (¬ A)
dni p u = u p

contraposition : {A B : Set} → (A → B) → (¬ B → ¬ A)
contraposition f p a = p (f a)

de-morgan₁ : {A B : Set} → ¬ (A ⊎ B) → ¬ A
de-morgan₁ p a = p (left a)

de-morgan₂ : {A B : Set} → ¬ (A ⊎ B) → ¬ B
de-morgan₂ p b = p (right b)

-- EXERCISE: prove some properties about lists

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

_∷'_ : {A : Set} → List A → A → List A
a ∷' b = {!!}

reverse : {A : Set} → List A → List A
reverse a = {!!}

_++_ : {A : Set} → List A → List A → List A
a ++ b = {!!}

lemma-reverse-∷' : {A : Set} → (ys : List A) (x : A) → reverse (ys ∷' x) ≡ (x ∷ reverse ys)
lemma-reverse-∷' a b = {!!}

lemma-reverse-reverse : {A : Set} → (xs : List A) → reverse (reverse xs) ≡ xs
lemma-reverse-reverse a = {!!}

data _≈_ {A : Set} : List A → List A → Set where

≡→≈ : {A : Set} {xs ys : List A} → xs ≡ ys → xs ≈ ys
≡→≈ a = {!!}

≈→≡ : {A : Set} {xs ys : List A} → xs ≈ ys → xs ≡ ys
≈→≡ a = {!!}

-- EXERCISE: prove some properties about vectors

data Vector (A : Set) : ℕ → Set where

drop : {A : Set} {n : ℕ} (k : ℕ) → Vector A (k + n) → Vector A n
drop a b = {!!}

take : {A : Set} {n : ℕ} (k : ℕ) → Vector A (k + n) → Vector A k
take a b = {!!}

_++ᵥ_ : {A : Set} {n m : ℕ} → Vector A n → Vector A m → Vector A (n + m)
a ++ᵥ b = {!!}

-- EXERCISE: Verify the following lemma.
lemma-take-drop : {A : Set} {n : ℕ} → (k : ℕ) → (xs : Vector A (k + n)) → (take k xs ++ᵥ drop k xs) ≡ xs
lemma-take-drop a b = {!!}
