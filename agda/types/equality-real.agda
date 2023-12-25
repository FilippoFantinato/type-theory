{-# OPTIONS --without-K #-}

module types.equality-real where

data _≡_ {A : Set} : A → A → Set where
  refl : (a : A) → a ≡ a


data ⊤ : Set where
  * : ⊤


lemma₀ : (p : * ≡ *) → (refl *) ≡ p
lemma₀ (refl *) = refl (refl *)
