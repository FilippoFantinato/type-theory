module types.times where

open import types.equality

-- Both A and B are inhabited
data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

fst : {A B : Set} → (z : A × B) → A
fst (x , y) = x

snd : {A B : Set} → (z : A × B) → B
snd (x , y) = y

η-conversion-× : {A B : Set} → (z : A × B) → ((fst z , snd z) ≡ z)
η-conversion-× (x , y) = refl (x , y)
