module exercises.lists where

open import types.natural-numbers
open import types.lists
open import types.equality


exampleListℕ : List ℕ
exampleListℕ = zero ∷ ((succ (succ zero)) ∷ ((succ zero) ∷ []))


module _ {A : Set} where

  _∷'_ : List A → A → List A
  [] ∷' y = y ∷ []
  (x ∷ xs) ∷' y = x ∷ (xs ∷' y)

  reverse : List A → List A
  reverse [] = []
  reverse (x ∷ xs) = (reverse xs) ∷' x

  lemma-reverse-∷' : (ys : List A) (x : A) → reverse (ys ∷' x) ≡ (x ∷ reverse ys)
  lemma-reverse-∷' [] x        = refl (x ∷ [])
  lemma-reverse-∷' (y ∷ ys) x = cong (λ zs → zs ∷' y) (lemma-reverse-∷' ys x)

  lemma-reverse-reverse : (xs : List A) → ((reverse (reverse xs)) ≡ xs)
  lemma-reverse-reverse []        = refl []
  lemma-reverse-reverse (x ∷ xs) =
    trans (lemma-reverse-∷' (reverse xs) x)
          (cong (λ zs → x ∷ zs) (lemma-reverse-reverse xs))

  _++_ : List A → List A → List A
  a ++ [] = a
  a ++ (x ∷ xs) = {!(a ∷' x) ++ xs!}

  ≡→≈ : {xs ys : List A} → xs ≡ ys → xs ≈ ys
  ≡→≈ (refl []) = both-empty
  ≡→≈ (refl (x ∷ p)) = both-same-cons (refl x) (≡→≈ (refl p))

  -- EXERCISE: Show that related lists are equal.
  ≈→≡ : {xs ys : List A} → (xs ≈ ys) → (xs ≡ ys)
  ≈→≡ both-empty = refl []
  ≈→≡ (both-same-cons (refl x) xs) = cong (λ xs → (x ∷ xs)) (≈→≡ xs)
