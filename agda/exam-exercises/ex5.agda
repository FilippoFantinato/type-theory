module exam.ex5 where

open import types.empty
open import types.natural-numbers
open import types.equality
open import types.even-odd

-- EQUALITY OF LISTS

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

module _ {A : Set} where
  -- the "snoc" operation ("backwards cons"),
  -- i.e. append an element at the end
  _∷ʳ_ : List A → A → List A
  []       ∷ʳ y = y ∷ []
  (x ∷ xs) ∷ʳ y = x ∷ (xs ∷ʳ y)

  -- for instance, "reverse (a ∷ b ∷ c ∷ [])" is "c ∷ b ∷ a ∷ []".
  reverse : List A → List A
  reverse []       = []
  reverse (x ∷ xs) = reverse xs ∷ʳ x

  -- EXERCISE: Verify the following lemma.
  lemma-reverse-∷ʳ : (ys : List A) (x : A) → reverse (ys ∷ʳ x) ≡ (x ∷ reverse ys)
  lemma-reverse-∷ʳ ys x = {!!}

  lemma-reverse-reverse : (xs : List A) → reverse (reverse xs) ≡ xs
  lemma-reverse-reverse xs = {!!}

  -- EXERCISE: State and prove that _++_ on lists is associative.
  _++_ : List A → List A → List A
  []       ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  -- The following relation relates exactly those lists which have the same length
  -- and whose corresponding entries are equal.
  data _≈_ : List A → List A → Set where
    both-empty     : [] ≈ []
    both-same-cons : {xs ys : List A} {x y : A} → x ≡ y → xs ≈ ys → (x ∷ xs) ≈ (y ∷ ys)

  -- EXERCISE: Show that equal lists are related by _≈_.
  ≡→≈ : {xs ys : List A} → xs ≡ ys → xs ≈ ys
  ≡→≈ p = {!!}

  -- EXERCISE: Show that related lists are equal.
  ≈→≡ : {xs ys : List A} → xs ≈ ys → xs ≡ ys
  ≈→≡ p = {!!}

-- EQUALITY OF VECTORS

data Vector (A : Set) : ℕ → Set where
  []  : Vector A zero
  _∷_ : {n : ℕ} → A → Vector A n → Vector A (succ n)

drop : {A : Set} {n : ℕ} (k : ℕ) → Vector A (k + n) → Vector A n
drop zero      xs        = xs
drop (succ k') (x ∷ xs') = drop k' xs'

take : {A : Set} {n : ℕ} (k : ℕ) → Vector A (k + n) → Vector A k
take zero      xs        = []
take (succ k') (x ∷ xs') = x ∷ take k' xs'

_++ᵥ_ : {A : Set} {n m : ℕ} → Vector A n → Vector A m → Vector A (n + m)
[]        ++ᵥ ys = ys
(x ∷ xs') ++ᵥ ys = x ∷ (xs' ++ᵥ ys)

-- EXERCISE: Verify the following lemma.
lemma-take-drop : {A : Set} {n : ℕ} → (k : ℕ) → (xs : Vector A (k + n)) → (take k xs ++ᵥ drop k xs) ≡ xs
lemma-take-drop = {!!}

-- EXERCISE: Find out where the difficulty is in stating that _++ᵥ_ on
-- vectors is associative.


-- EXERCISE: Define a predicate "AllEven" for lists of natural numbers
-- such that "AllEven xs" is inhabited if and only if all entries of the list "xs" are even.
-- By convention, the empty list counts as consisting of even-only elements.
data AllEven : List ℕ → Set where
  {- supply appropriate clauses here -}

data Dec (X : Set) : Set where
  yes : X       → Dec X
  no  : (X → ⊥) → Dec X

data _⊎_ (A B : Set) : Set where
  left  : A → A ⊎ B
  right : B → A ⊎ B

lemma-even-odd' : (a : ℕ) → Even a ⊎ Odd a
lemma-even-odd' = {!!}

lemma-odd-and-even' : {a : ℕ} → Odd a → Even a → ⊥
lemma-odd-and-even' (step-odd q) (step-even p) = lemma-odd-and-even q p


-- EXERCISE: Fill this hole, establishing that the property for
-- a number to be even is decidable.
even?' : (n : ℕ) → Dec (Even n)
even?' n = {!!}

-- EXERCISE: Fill this hole, establishing that the property for
-- a list of numbers to consist only of even numbers is decidable.
all-even? : (xs : List ℕ) → Dec (AllEven xs)
all-even? xs = {!!}

-- EXERCISE: Show that the sum of the elements of a list satisfying "AllEven" is even.
sum : List ℕ → ℕ
sum []       = zero
sum (x ∷ xs) = x + sum xs

lemma-+-even : {a b : ℕ} → Even a → Even b → Even (a + b)
lemma-+-even p q = {!!}

sum-is-even : (xs : List ℕ) → AllEven xs → Even (sum xs)
sum-is-even xs p = {!!}


-- EXERCISE: Define a predicate "All P" for lists of elements of some type A
-- and predicates "P : A → Set" such that "All P xs" is inhabited if
-- and only if all entries of the list "xs" satisfy P.
-- The special case "All Even" should coincide with the predicate
-- "AllEven" from the previous exercise.
data All {A : Set} (P : A → Set) : List A → Set where
  {- give appropriate clauses -}

-- EXERCISE: Define a predicate "Any P" for lists of elements of some type A
-- and predicates "P : A → Set" such that "Any P xs" is inhabited if
-- and only if at least one entry of the list "xs" satisfies P.
data Any {A : Set} (P : A → Set) : List A → Set where
  {- give appropriate clauses -}

-- EXERCISE: Define a relation "_∈_" such that "x ∈ ys" is the type
-- of witnesses that x occurs in the list ys.
data _∈_ {A : Set} : A → List A → Set where
  {- give appropriate clauses -}

-- EXERCISE: Show that "x ∈ ys" if and only if "Any (_≡_ x) ys".
∈-to-Any : {A : Set} {x : A} {ys : List A} → x ∈ ys → Any (_≡_ x) ys
∈-to-Any = {!!}

Any-to-∈ : {A : Set} {x : A} {ys : List A} → Any (_≡_ x) ys → x ∈ ys
Any-to-∈ = {!!}
