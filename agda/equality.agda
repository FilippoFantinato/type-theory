module equality where

open import natural-numbers


data _≡_ {X : Set} : X → X → Set where
  refl : (a : X) → (a ≡ a)


-- zero ≡ zero is the type of witnesses that zero equals zero
-- zero ≡ succ zero is the type of witnesses that zero equals succ zero (this must be empty)
lemma-zero-identity : zero ≡ zero
lemma-zero-identity = refl zero


lemma-zero-+ : (b : ℕ) → ((zero + b) ≡ b)
lemma-zero-+ b = refl b


cong : {A B : Set} → {x y : A} → (f : A → B) → x ≡ y → (f x) ≡ (f y)
cong f (refl a) = refl (f a)


lemma-+-zero : (a : ℕ) → ((a + zero) ≡ a)
lemma-+-zero zero = lemma-zero-identity
lemma-+-zero (succ a) = cong succ (lemma-+-zero a)


symm : {A : Set} → {x y : A} → (x ≡ y) → (y ≡ x)
symm (refl a) = refl a


trans : {A : Set} → {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans (refl a) (refl a) = refl a


lemma-+-succ : (a b : ℕ) → ((a + (succ b)) ≡ succ (a + b))
lemma-+-succ zero b     = refl (succ b)
lemma-+-succ (succ a) b = cong succ (lemma-+-succ a b)


lemma-+-commutative : (a b : ℕ) → ((a + b) ≡ (b + a))
lemma-+-commutative zero b = symm (lemma-+-zero b)
lemma-+-commutative (succ a) b =
  trans (cong succ (lemma-+-commutative a b)) (symm (lemma-+-succ b a))
