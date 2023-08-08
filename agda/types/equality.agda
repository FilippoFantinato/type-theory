module types.equality where

open import types.natural-numbers

infix 4 _≡_

data _≡_ {A : Set} : A → A → Set where
  refl : (a : A) → (a ≡ a)

{-# BUILTIN EQUALITY _≡_ #-}

infix  1 begin_
infixr 2 _≡⟨⟩_ _≡⟨_⟩_
infix  3 _∎

cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → (f x) ≡ (f y)
cong f (refl a) = refl (f a)

symm : {A : Set} {x y : A} → (x ≡ y) → (y ≡ x)
symm (refl a) = refl a

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans (refl _) (refl q) = refl q

transport : {A B : Set} {x y : A} → (F : A → Set) → x ≡ y → F x → F y
transport F (refl s) = λ s → s

-- EXERCISE: Prove that equal functions have equal values. (The
-- converse is a principle known as "function extensionality" which
-- can be postulated in Agda but not assumed by default)
equal→pwequal : {A B : Set} → {f g : A → B} {x : A} → (f ≡ g) → ((f x) ≡ (g x))
equal→pwequal (refl f) = refl (f _)

{- equal-pwequal : {f g : A → B} {x : A} → (f ≡ g) → ((f x) ≡ (g x))
equal-pwequal p rewrite p = {!!} -}

begin_ : {A : Set} {x y : A} → x ≡ y → x ≡ y
begin p = p

_≡⟨_⟩_ : {A : Set} {y z : A} → (x : A) → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ p ⟩ q = trans p q

_≡⟨⟩_ : {A : Set} {y : A} → (x : A) → (q : x ≡ y) → x ≡ y
x ≡⟨⟩ q = q

_∎ : {A : Set} → (x : A) → x ≡ x
x ∎ = refl x
