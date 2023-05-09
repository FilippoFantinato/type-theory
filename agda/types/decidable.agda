module types.decidable where

open import types.empty

-- Dec A is the type of witnesses that A is decidable, 
-- so whether A is inhabited or empty
-- Dec A is isomorphic to A ⊎ (¬ A)
data Dec (A : Set) : Set where
  yes :   A → Dec A
  no  : ¬ A → Dec A

