module exercises.equality where

open import types.equality

-- Same witness
UIP : {A : Set} {x y : A} → (p q : x ≡ y) → p ≡ q
UIP (refl _) (refl _) = refl _
