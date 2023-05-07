module types.equality where

open import types.natural-numbers

infix 5 _≡_
data _≡_ {X : Set} : X → X → Set where
  refl : (a : X) → (a ≡ a)


{-# BUILTIN EQUALITY _≡_ #-}


cong : {A B : Set} → {x y : A} → (f : A → B) → x ≡ y → (f x) ≡ (f y)
cong f (refl a) = refl (f a)

symm : {A : Set} → {x y : A} → (x ≡ y) → (y ≡ x)
symm (refl a) = refl a

trans : {A : Set} → {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans (refl a) (refl a) = refl a

transport : {A : Set} {x y : A} → (F : A → Set) → x ≡ y → F x → F y
transport F (refl s) = λ s → s 

-- EXERCISE: Prove that equal functions have equal values. (The
-- converse is a principle known as "function extensionality" which
-- can be postulated in Agda but not assumed by default)
equal→pwequal : {A B : Set} {f g : A → B} {x : A} → (f ≡ g) → ((f x) ≡ (g x))
equal→pwequal (refl f) = refl (f _)

{- equal-pwequal : {A B : Set} {f g : A → B} {x : A} → (f ≡ g) → ((f x) ≡ (g x))
equal-pwequal p rewrite p = {!!} -}
