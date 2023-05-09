module exercises.insertion-sort where

open import types.lists
open import types.sum
open import types.booleans

-- Two methods for veryfing the an algorithm
-- (1) First implement then separately verify its correctness
-- (2) Correct by construction

-- insertion-sort : {A : Set} → List A → List A
-- insertion-sort = {!!}


module implementation
  {A : Set}
  (_≤_ : A → A → Set)
  (cmp : (x y : A) → (x ≤ y) ⊎ (y ≤ x)) where

  insert : A → List A → List A
  insert x [] = x ∷ []
  insert x (y ∷ ys) with cmp x y
  ... | left l = x ∷ (y ∷ ys)
  ... | right r = y ∷ (insert x ys)

  sort : List A → List A
  sort []        = []
  sort (x ∷ xs) = insert x (sort xs)


module verification
  {A : Set}
  (_≤_ : A → A → Set)
  (cmp : (x y : A) → (x ≤ y) ⊎ (y ≤ x)) where

  open implementation _≤_ cmp

  data IsOrdered : List A → Set where
    empty     : IsOrdered []
    singleton : {x : A} → IsOrdered (x ∷ [])
    cons      : {x y : A} {ys : List A} → x ≤ y → IsOrdered (y ∷ ys) → IsOrdered (x ∷ (y ∷ ys))

  lemma₀ : (x y : A) (ys : List A) → y ≤ x → IsOrdered (y ∷ ys) → IsOrdered (y ∷ insert x ys)
  lemma₀ x y [] y≤x p = cons y≤x singleton
  lemma₀ x y (z ∷ ys) y≤x (cons y≤z q) with cmp x z
  ... | left  x≤z = cons y≤x (cons x≤z q)
  ... | right z≤x = cons y≤z (lemma₀ x z ys z≤x q)

  lemma : (x : A) (y : List A) → IsOrdered y → IsOrdered (insert x y)
  lemma x [] p = singleton
  lemma x (y ∷ ys) p with cmp x y
  ... | left x≤y = cons x≤y p
  ... | right y≤x = lemma₀ x y ys y≤x p

  theorem : (xs : List A) → IsOrdered (sort xs)
  theorem [] = empty
  theorem (x ∷ xs)  = lemma x (sort xs) (theorem xs)

  cheatsort : List A → List A
  cheatsort xs = []

  cheattheorem : (xs : List A) → IsOrdered (cheatsort xs)
  cheattheorem xs = empty

module correct-by-construction
  {A : Set}
  {_≤_ : A → A → Set}
  {min : A}
  {min≤ : {x : A} → (min ≤ x)}
  {cmp : (x y : A) → (x ≤ y) ⊎ (y ≤ x)} where

  data OList (l : A) : Set where
    nil : OList l
    cons : (x : A) → l ≤ x → OList x → OList l

  {- toList : {l : A} → OList l → List A
  toList nil = []
  toList (cons x p xs) = x ∷ (toList xs) -}

  insert : {l : A} → (x : A) → l ≤ x → OList l → OList l
  insert x l≤x nil = cons x l≤x nil
  insert x l≤x (cons y l≤y ys) with (cmp x y)
  ... | left  x≤y = cons x l≤x (cons y x≤y ys)
  ... | right y≤x = cons y l≤y (insert x y≤x ys)

  sort : List A → OList min
  sort [] = nil
  sort (x ∷ xs) = insert x min≤ (sort xs)


  cheatsort : List A → OList min
  cheatsort xs = nil
