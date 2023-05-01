module lists where

open import natural-numbers
open import equality


data List (X : Set) : Set where
  []   : List X
  _::_ : X → List X → List X


exampleListℕ : List ℕ
exampleListℕ = zero :: ((succ (succ zero)) :: ((succ zero) :: []))



module _ {A : Set} where

  _::'_ : List A → A → List A
  [] ::' y = y :: []
  (x :: xs) ::' y = x :: (xs ::' y)

  reverse : List A → List A
  reverse [] = []
  reverse (x :: xs) = (reverse xs) ::' x

  lemma-reverse-::' : (ys : List A) (x : A) → reverse (ys ::' x) ≡ (x :: reverse ys)
  lemma-reverse-::' [] x        = refl (x :: [])
  lemma-reverse-::' (y :: ys) x = cong (λ zs → zs ::' y) (lemma-reverse-::' ys x)

  lemma-reverse-reverse : (xs : List A) → ((reverse (reverse xs)) ≡ xs)
  lemma-reverse-reverse []        = refl []
  lemma-reverse-reverse (x :: xs) =
    trans (lemma-reverse-::' (reverse xs) x)
          (cong (λ zs → x :: zs) (lemma-reverse-reverse xs))
