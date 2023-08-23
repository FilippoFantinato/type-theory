module types.top where

open import types.equality

data ⊤ : Set where
  * : ⊤

only-one-element : (x : ⊤) → (y : ⊤) → x ≡ y
only-one-element * * = refl *

same-proof : {x y : ⊤} → (z₁ : x ≡ y) → (z₂ : x ≡ y) → z₁ ≡ z₂
same-proof (refl _) (refl w) = refl (refl w)
