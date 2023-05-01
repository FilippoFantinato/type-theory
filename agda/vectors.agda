module vectors where

open import natural-numbers


data Vector (A : Set) : ℕ → Set where
  [] : Vector A zero
  _::_ : {n : ℕ} → A → Vector A n → Vector A (succ n)

-- EXERCISE: Define a function which computes the length of a given vector.
lengthV : {n : ℕ} {A : Set} → Vector A n → ℕ
lengthV [] = zero
lengthV (x :: xs) = succ (lengthV xs)

lengthV' : {n : ℕ} {A : Set} → Vector A n → ℕ
lengthV' {n} {A} xs = n


-- EXERCISE: Define the map function for vectors
mapV : {n : ℕ} {A B : Set} → (A → B) → Vector A n → Vector B n
mapV f [] = []
mapV f (x :: xs) = (f x) :: (mapV f xs)


-- EXERCISE: Define these vector functions
zipWithV : {A B C : Set} {n : ℕ} → (A → B → C) → Vector A n → Vector B n → Vector C n
zipWithV f []       []         = [] 
zipWithV f (x :: xs) (y :: ys) = (f x y) :: (zipWithV f xs ys)


-- For instance, "dropV (succ zero) (a ∷ b ∷ c ∷ [])" should evaluate to "b ∷ c ∷ []".
dropV : {A : Set} {n : ℕ} (k : ℕ) → Vector A (k + n) → Vector A n
dropV zero xs            = xs
dropV (succ n) (x :: xs) = dropV n xs


-- For instance, "takeV (succ zero) (a ∷ b ∷ c ∷ [])" should evaluate to "a ∷ []"
takeV : {A : Set} {n : ℕ} (k : ℕ) → Vector A (k + n) → Vector A k
takeV zero _             = []
takeV (succ n) (x :: xs) = x :: (takeV n xs)


-- For instance, "snocV (a ∷ b ∷ []) c" should evaluate to "a ∷ b ∷ c ∷ []".
snocV : {A : Set} {n : ℕ} → Vector A n → A → Vector A (succ n)
snocV [] y = y :: []
snocV (x :: []) y = x :: (y :: [])
snocV (x :: xs) y = (x :: (snocV xs y))


-- For instance, "(a ∷ b ∷ []) ++ (c ∷ d ∷ [])" should evaluate to "a ∷ b ∷ c ∷ d ∷ []".
_++_ : {A : Set} {n m : ℕ} → Vector A n → Vector A m → Vector A (n + m)
[] ++ y = y
(x :: xs) ++ y = x :: (xs ++ y)


-- For instance, "reverseV (a ∷ b ∷ c ∷ [])" should evaluate to "c ∷ b ∷ a ∷ []".
reverseV : {A : Set} {n : ℕ} → Vector A n → Vector A n
reverseV [] = []
reverseV (x :: (y :: [])) = y :: (x :: [])
reverseV (x :: xs) = snocV (reverseV xs) x 


-- For instance, "concatV ((a ∷ b ∷ []) ∷ (c ∷ d ∷ []) ∷ [])" should evlauate to
-- "a ∷ b ∷ c ∷ d ∷ []".
concatV : {A : Set} {n m : ℕ} → Vector (Vector A n) m → Vector A (m · n)
concatV [] = []
concatV (xs :: xss) = {!xs ++ (concatV xss)!}
