module exam-exercises.ex5 where

open import types.empty
open import types.natural-numbers
open import types.equality
open import types.even-odd

-- EQUALITY OF LISTS

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

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
