module exercises.tautologies where

open import types.equality
open import types.empty
open import types.sum

------------------------------------
----[ LOGICAL TAUTOLOGIES ]---------
------------------------------------

¬ : Set → Set
¬ X = (X → ⊥)

dni : {A : Set} → A → ¬ (¬ A)
dni ¬ p = {! !}

contraposition : {A B : Set} → (A → B) → (¬ B → ¬ A)
contraposition f = {!!}

de-morgan₁ : {A B : Set} → (¬ (A ⊎ B)) → (¬ A)
de-morgan₁ p a = {!!}

de-morgan₂ : {A B : Set} → ¬ (A ⊎ B) → ¬ B
de-morgan₂ = {!!}
