module types.all-even where

open import types.lists
open import types.natural-numbers
open import types.even-odd
open import types.decidable


data AllEven : List ℕ → Set where
  empty : AllEven []
  cons  : {x : ℕ} {xs : List ℕ} → Even x → AllEven xs → AllEven (x ∷ xs)

all-even? : (xs : List ℕ) → Dec (AllEven xs)
all-even? [] = yes empty
all-even? (x ∷ xs)  with even? x with all-even? xs
... | yes p | yes f = yes (cons p f)
... | yes p | no  g = {!!}
... | no q  | _ = no λ { (cons r _) → q r}
