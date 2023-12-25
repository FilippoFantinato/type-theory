{-# OPTIONS --without-K #-}

module types.top where 

data _≡_ {A : Set} : A → A → Set where
  refl : (x : A) → x ≡ x

symm : {A : Set} {a b : A} → a ≡ b → b ≡ a
symm (refl p) = refl p

data Unit : Set where
  * : Unit

UIP-⊤ : {y₁ y₂ : Unit} → (z₁ : y₁ ≡ y₂) → (z₂ : y₁ ≡ y₂) → z₁ ≡ z₂
UIP-⊤ (refl *) (refl x) = refl (refl x)

{-
UIP-A : {A : Set} {y₁ y₂ : A} → (z₁ : y₁ ≡ y₂) → (z₂ : y₁ ≡ y₂) → z₁ ≡ z₂
UIP-A (refl _) (refl x) = refl (refl x)
-}

only-one-element : (x : Unit) → (y : Unit) → x ≡ y
only-one-element * * = (refl *)

postulate
  I_IdUni : {A : Set} → (a : A) → (q : a ≡ a) → q ≡ (refl a)

UIP-A : {A : Set} {y₁ y₂ : A} → (z₁ : y₁ ≡ y₂) → (z₂ : y₁ ≡ y₂) → z₁ ≡ z₂
UIP-A (refl x) z₂ = symm (I_IdUni x z₂)

