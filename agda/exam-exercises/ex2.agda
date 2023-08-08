module exam.ex2 where

open import types.natural-numbers
open import types.equality

-- Define the List type
data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

-- Define a function sum which sums all numbers in the given list
sum : List ℕ → ℕ
sum [] = zero
sum (x ∷ xs) = zero + sum xs

-- Define some well-known functions about lists
map : {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

zip : {A B C : Set} → (A → B → C) → List A → List B → List C
zip f [] []             = []
zip f [] (y ∷ ys)       = []
zip f (x ∷ xs) []       = []
zip f (x ∷ xs) (y ∷ ys) = f x y ∷ zip f xs ys

-- Define the Vector type
data Vector (A : Set) : ℕ → Set where
  []  : Vector A zero
  _∷_ : {n : ℕ} → A → Vector A n → Vector A (succ n)


-- Define some useful functions about vectors
lengthV : {A : Set} {n : ℕ} → Vector A n → ℕ
lengthV {_} {n} x = n

mapV : {n : ℕ} {A B : Set} → (A → B) → Vector A n → Vector B n
mapV f [] = []
mapV f (x ∷ xs) = f x ∷ mapV f xs

zipWithV : {n : ℕ} {A B C : Set} → (A → B → C) → Vector A n → Vector B n → Vector C n
zipWithV f [] [] = []
zipWithV f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWithV f xs ys

dropV : {A : Set} {n : ℕ} → (k : ℕ) → Vector A (k + n) → Vector A n
dropV zero v = v
dropV (succ k) (x ∷ xs) = dropV k xs

takeV : {A : Set} {n : ℕ} → (k : ℕ) → Vector A (k + n) → Vector A k
takeV zero x = []
takeV (succ k) (x ∷ xs) = x ∷ takeV k xs

_++_ : {A : Set} {n m : ℕ} → Vector A n → Vector A m → Vector A (n + m)
[] ++ y = y
(x ∷ xs) ++ y = x ∷ (xs ++ y)

snocV : {A : Set} {n : ℕ} → Vector A n → A → Vector A (succ n)
snocV [] y = y ∷ []
snocV (x ∷ xs) y = x ∷ snocV xs y

reverseV : {A : Set} {n : ℕ} → Vector A n → Vector A n
reverseV [] = []
reverseV (x ∷ xs) = snocV (reverseV xs) x

concatV : {A : Set} {n m : ℕ} →  Vector (Vector A n) m → Vector A (m · n)
concatV [] = []
concatV (x ∷ xs) = x ++ concatV xs

lemma-take-drop : {A : Set} {n : ℕ} → (k : ℕ) → (x : Vector A (k + n)) → (takeV k x ++ dropV k x) ≡ x
lemma-take-drop zero x = refl x
lemma-take-drop (succ k) (x ∷ xs) = cong (λ xs → x ∷ xs) (lemma-take-drop k xs)
