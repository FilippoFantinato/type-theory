module exam-exercises-2.ex5 where

open import types.empty
open import types.natural-numbers
open import types.equality
open import types.even-odd
open import types.sum

-- EQUALITY OF LISTS

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

-- EXERCISE: Define a predicate "AllEven" for lists of natural numbers
-- such that "AllEven xs" is inhabited if and only if all entries of the list "xs" are even.
-- By convention, the empty list counts as consisting of even-only elements.
data AllEven : List ℕ → Set where
  {- supply appropriate clauses here -}
  base-all-even : AllEven []
  step-all-even : {x : ℕ} {xs : List ℕ} → Even x → AllEven xs → AllEven (x ∷ xs)

data Dec (X : Set) : Set where
  yes : X        → Dec X
  no  : (X → ⊥) → Dec X

{- }data _⊎_ (A B : Set) : Set where
  left  : A → A ⊎ B
  right : B → A ⊎ B
-}

lemma-odd-and-even' : {a : ℕ} → Odd a → Even a → ⊥
lemma-odd-and-even' (step-odd q) (step-even p) = lemma-odd-and-even' q p


-- EXERCISE: Fill this hole, establishing that the property for
-- a number to be even is decidable.
even?' : (n : ℕ) → Dec (Even n)
even?' n with lemma-even-odd n
... | left x  = yes x
... | right x = no (lemma-odd-and-even' x)

-- EXERCISE: Fill this hole, establishing that the property for
-- a list of numbers to consist only of even numbers is decidable.
lemma-odd-all-even : {n : ℕ} {xs : List ℕ} → Odd n → AllEven xs → ⊥
lemma-odd-all-even x = {!!}


all-even? : (xs : List ℕ) → Dec (AllEven xs)
all-even? []       = yes base-all-even
all-even? (x ∷ xs) with all-even? xs with lemma-even-odd x
... | yes xs | left x  = yes (step-all-even x xs)
... | yes xs | right x = no (lemma-odd-all-even x)
... | no xs  | _ = {!!}

-- EXERCISE: Show that the sum of the elements of a list satisfying "AllEven" is even.
sum : List ℕ → ℕ
sum []       = zero
sum (x ∷ xs) = x + sum xs

lemma-+-even : {a b : ℕ} → Even a → Even b → Even (a + b)
lemma-+-even base-even q = q
lemma-+-even (step-even p) q = step-even (lemma-+-even p q)

sum-is-even : {xs : List ℕ} → AllEven xs → Even (sum xs)
sum-is-even base-all-even = base-even
sum-is-even (step-all-even x xs) = {!!}


-- EXERCISE: Define a predicate "All P" for lists of elements of some type A
-- and predicates "P : A → Set" such that "All P xs" is inhabited if
-- and only if all entries of the list "xs" satisfy P.
-- The special case "All Even" should coincide with the predicate
-- "AllEven" from the previous exercise.
data All {A : Set} (P : A → Set) : List A → Set where
  {- give appropriate clauses -}
  empty-all : All P []
  cons-all  : {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)

-- EXERCISE: Define a predicate "Any P" for lists of elements of some type A
-- and predicates "P : A → Set" such that "Any P xs" is inhabited if
-- and only if at least one entry of the list "xs" satisfies P.
data Any {A : Set} (P : A → Set) : List A → Set where
  {- give appropriate clauses -}
  here-any  : {x : A} → P x → (xs : List A) → Any P (x ∷ xs)
  there-any : {xs : List A} → (x : A) → Any P xs → Any P (x ∷ xs)

-- EXERCISE: Define a relation "_∈_" such that "x ∈ ys" is the type
-- of witnesses that x occurs in the list ys.
data _∈_ {A : Set} : A → List A → Set where
  {- give appropriate clauses -}
  here  : (x : A) → (xs : List A) → x ∈ (x ∷ xs)
  there : {x : A} {xs : List A} → (y : A) → x ∈ xs → x ∈ (y ∷ xs)

-- EXERCISE: Show that "x ∈ ys" if and only if "Any (_≡_ x) ys".
∈-to-Any : {A : Set} {x : A} {ys : List A} → x ∈ ys → Any (_≡_ x) ys
∈-to-Any (here x xs) = here-any (refl x) xs
∈-to-Any (there y p) = there-any y (∈-to-Any p)

Any-to-∈ : {A : Set} {x : A} {ys : List A} → Any (_≡_ x) ys → x ∈ ys
Any-to-∈ (here-any (refl x) xs) = here x xs
Any-to-∈ (there-any x p)        = there x (Any-to-∈ p)
