module exercises.singleton where

open import types.equality

module _ {A : Set} where
  data ⊤ : Set where
    * : ⊤

  all-same-element : (x : ⊤) → (y : ⊤) → x ≡ y
  all-same-element * * = refl _
