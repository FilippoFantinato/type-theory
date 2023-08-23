module exam-exercises-2.ex2 where

open import types.natural-numbers

-- Define the List type
data List (A : Set) : Set where

-- Define a function sum which sums all numbers in the given list
sum : List ℕ → ℕ
sum a = {!!}

-- Define some well-known functions about lists
map : {A B : Set} → (A → B) → List A → List B
map f a = {!!}

zip : {A B C : Set} → (A → B → C) → List A → List B → List C
zip f a b = {!!}


-- Define the Vector type
data Vector (A : Set) : ℕ → Set where


-- Define some useful functions about vectors
lengthV : {A : Set} {n : ℕ} → Vector A n → ℕ
lengthV x = {!!}

mapV : {n : ℕ} {A B : Set} → (A → B) → Vector A n → Vector B n
mapV f a = {!!}

zipWithV : {n : ℕ} {A B C : Set} → (A → B → C) → Vector A n → Vector B n → Vector C n
zipWithV f a b = {!!}

dropV : {A : Set} {n : ℕ} → (k : ℕ) → Vector A (k + n) → Vector A n
dropV a b = {!!}

takeV : {A : Set} {n : ℕ} → (k : ℕ) → Vector A (k + n) → Vector A k
takeV a b = {!!}

_++_ : {A : Set} {n m : ℕ} → Vector A n → Vector A m → Vector A (n + m)
a ++ b = {!!}

snocV : {A : Set} {n : ℕ} → Vector A n → A → Vector A (succ n)
snocV a b = {!!}

reverseV : {A : Set} {n : ℕ} → Vector A n → Vector A n
reverseV a = {!!}

concatV : {A : Set} {n m : ℕ} →  Vector (Vector A n) m → Vector A (m · n)
concatV a = {!!}
