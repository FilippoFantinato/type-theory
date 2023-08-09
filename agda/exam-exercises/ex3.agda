{-# OPTIONS --allow-unsolved-metas #-}

module exam-exercises.ex3 where

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
  refl : (x : X) → x ≡ x
-}

-- Define some generalities on equality
-- EXERCISE: Fill in this hole, thereby proving that equality is a "congruence";
-- by this lemma, we can apply the same operation to the two sides of an equation
-- and still be sure that the equation holds.
cong' : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong' f (refl x) = refl (f x)

symm' : {A : Set} {x y : A} → x ≡ y → y ≡ x
symm' (refl x) = refl x

-- EXERCISE: Fill in this hole, thereby proving that equality is transitive.
trans' : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans' (refl _) p = p

-- EXERCISE: Prove that equal functions have equal values. (The
-- converse is a principle known as "function extensionality" which
-- can be postulated in Agda but is not assumed by default.)
equal→pwequal' : {A B : Set} {f g : A → B} → (x : A) → f ≡ g → f x ≡ g x
equal→pwequal' x (refl f) = refl (f x)

-- EXERCISE: Think about the expression "(⊥ ≡ ℕ)". Is it well-defined?
-- What would be its meaning?

-- EXERCISE: Fill in this hole. This lemma will be used below
-- in the proof that the double of any number is even.
transport' : {A : Set} {x y : A} → (F : A → Set) → x ≡ y → F x → F y
transport' F (refl p) s = s

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
[]       ∷' y = y ∷ []
(x ∷ xs) ∷' y = x ∷ (xs ∷' y)

reverse : {A : Set} → List A → List A
reverse []       = []
reverse (x ∷ xs) = reverse xs ∷' x

_++_ : {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

lemma-reverse-∷' : {A : Set} → (ys : List A) (x : A) → reverse (ys ∷' x) ≡ (x ∷ reverse ys)
lemma-reverse-∷' [] x = refl (x ∷ [])
lemma-reverse-∷' (y ∷ ys) x = begin
  reverse ((y ∷ ys) ∷' x) ≡⟨⟩
  reverse (y ∷ (ys ∷' x)) ≡⟨⟩
  reverse (ys ∷' x) ∷' y  ≡⟨ cong (λ l → l ∷' y) (lemma-reverse-∷' ys x) ⟩
  (x ∷ reverse ys) ∷' y   ≡⟨⟩
  x ∷ reverse (y ∷ ys)    ≡⟨⟩
  x ∷ (reverse ys ∷' y)   ∎

lemma-reverse-reverse : {A : Set} → (xs : List A) → reverse (reverse xs) ≡ xs
lemma-reverse-reverse [] = refl []
lemma-reverse-reverse (x ∷ xs) = trans (lemma-reverse-∷' (reverse xs) x) (cong (λ zs → x ∷ zs) (lemma-reverse-reverse xs))

data _≈_ {A : Set} : List A → List A → Set where
  both-empty     : [] ≈ []
  both-same-cons : {xs ys : List A} {x y : A} → x ≡ y → xs ≈ ys → (x ∷ xs) ≈ (y ∷ ys)

≡→≈ : {A : Set} {xs ys : List A} → xs ≡ ys → xs ≈ ys
≡→≈ (refl []) = both-empty
≡→≈ (refl (x ∷ xs)) = both-same-cons (refl x) (≡→≈ (refl xs))

≈→≡ : {A : Set} {xs ys : List A} → xs ≈ ys → xs ≡ ys
≈→≡ both-empty = refl []
≈→≡ (both-same-cons (refl x) xs) = cong (λ l → x ∷ l) (≈→≡ xs)

-- EXERCISE: prove some properties about vectors

data Vector (A : Set) : ℕ → Set where
  []  : Vector A zero
  _∷_ : {n : ℕ} → A → Vector A n → Vector A (succ n)

drop : {A : Set} {n : ℕ} (k : ℕ) → Vector A (k + n) → Vector A n
drop zero      xs        = xs
drop (succ k') (x ∷ xs') = drop k' xs'

take : {A : Set} {n : ℕ} (k : ℕ) → Vector A (k + n) → Vector A k
take zero      xs        = []
take (succ k') (x ∷ xs') = x ∷ take k' xs'

_++ᵥ_ : {A : Set} {n m : ℕ} → Vector A n → Vector A m → Vector A (n + m)
[]        ++ᵥ ys = ys
(x ∷ xs') ++ᵥ ys = x ∷ (xs' ++ᵥ ys)

-- EXERCISE: Verify the following lemma.
lemma-take-drop : {A : Set} {n : ℕ} → (k : ℕ) → (xs : Vector A (k + n)) → (take k xs ++ᵥ drop k xs) ≡ xs
lemma-take-drop zero xs = refl xs
lemma-take-drop (succ k) (x ∷ xs) = cong (λ xs → x ∷ xs) (lemma-take-drop k xs)
