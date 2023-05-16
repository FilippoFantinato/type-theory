{-# OPTIONS --safe #-}

module exercises.termination where

open import types.equality
open import types.natural-numbers


-- Fo agda is not well-founded recursion, because it doesn't know that half (succ n) is much more smaller than (succ n)
-- digits : ℕ → ℕ
-- digits zero     = zero
-- digits (succ n) = succ (digits (half (succ n)))


-- Five options how to deal with this issue:
-- 1. {-# TERMINATING #-}, but won't work with {-# OPTIONS --safe #-}
-- 2. {-# NON_TERMINATING #-}, but same as above
-- 3. rewrite function, employ a different algorithm
-- 4. use a poor version of gas
-- 5. use a sophisticated version of gas ("well-founded induction")

module Option-1 where
  -- Just a promise that this function will terminate, but it's a bad practice
  {-# TERMINATING #-}
  digits : ℕ → ℕ
  digits zero     = zero
  digits (succ n) = succ (digits (half (succ n)))

  lemma-digits : (n : ℕ) → digits (succ n) ≡ succ (digits (half (succ n)))
  lemma-digits n = refl (digits (succ n))

  _ : digits (succ (succ (succ (succ zero)))) ≡ succ (succ (succ zero))
  _ = refl (digits (succ (succ (succ (succ zero)))))

  _ : digits (succ (succ (succ zero))) ≡ succ (succ zero)
  _ = refl (succ (succ zero)) -- refl


module Option-2 where
  -- State that this function won't terminate and so agda will never try to reduce terms
  -- to normal forms
  {-# NON_TERMINATING #-}
  digits : ℕ → ℕ
  digits zero     = zero
  digits (succ n) = succ (digits (half (succ n)))


module Option-3 where
  data Bin : Set where
    [] : Bin
    _O : Bin → Bin
    _I : Bin → Bin

  -- For instance: the number 6 (binary 110) is encoded as [] I I O

  decode : Bin → ℕ
  decode [] = zero
  decode (xs O) = (decode xs) · (succ (succ zero))
  decode (xs I) = (decode xs) · (succ (succ zero)) + (succ zero)

  succ' : Bin → Bin
  succ' []     = [] I
  succ' (xs O) = xs I
  succ' (xs I) = (succ' xs) O

  encode : ℕ → Bin
  encode zero = []
  encode (succ n) = succ' (encode n)

  length : Bin → ℕ
  length [] = zero
  length (xs O) = succ (length xs)
  length (xs I) = succ (length xs)

  digits : ℕ → ℕ
  digits n = length (encode n)

module Option-4 where
  digits : ℕ → ℕ
  digits n = go n n
    where
    go : ℕ → ℕ → ℕ
    go zero     gas        = zero
    go (succ x) zero       = zero
    go (succ x) (succ gas) = succ (go (half (succ x)) gas)

  _ : digits (succ (succ (succ zero))) ≡ succ (succ zero)
  _ = refl (succ (succ zero))

module Option-4' where
  data Maybe (X : Set) : Set where
    nothing : Maybe X
    just    : X → Maybe X

  succ' : Maybe ℕ → Maybe ℕ
  succ' nothing = nothing
  succ' (just n) = just (succ n)

  go : ℕ → ℕ → Maybe ℕ
  go zero     gas        = just zero
  go (succ x) zero       = nothing
  go (succ x) (succ gas) = succ' (go (half (succ x)) gas)

  digits : ℕ → Maybe ℕ
  digits n = go n n

  _ : digits (succ (succ (succ zero))) ≡ (just (succ (succ zero)))
  _ = {!!}


module Option-5 where
  data _<_ : ℕ → ℕ → Set where
    base : {n : ℕ} → n < (succ n)
    step : {a b : ℕ} → (a < b) → a < (succ a)

  -- The type "Acc x" is the type of witnesses that the number x is "accessible"
  data Acc : ℕ → Set where
    acc : {x : ℕ} → ((y : ℕ) → (y < x) → Acc y) → Acc x

  -- The number zero is accessible, because all its predecessors (no one)
  -- are accessible
  lemma-zero-is-accessible : Acc zero
  lemma-zero-is-accessible = acc (λ y ())

  -- lemma-one-is-accessible : Acc (succ zero)
  -- lemma-one-is-accessible = acc (λ { zero base → lemma-zero-is-accessible})

  theorem-ℕ-well-founded : (n : ℕ) → Acc n
  theorem-ℕ-well-founded zero   = lemma-zero-is-accessible
  theorem-ℕ-well-founded (succ n) = {!!}


  lemma-half< : (n : ℕ) → (half (succ n)) < (succ n)
  lemma-half< zero     = base
  lemma-half< (succ n) = {!!}


  go : (n : ℕ) → Acc n → ℕ
  go zero gas = zero
  go (succ n) (acc f) = succ (go (half (succ n)) (f (half (succ n)) (lemma-half< n)))


  digits : ℕ → ℕ
  digits n = go n (theorem-ℕ-well-founded n)

  lemma-digits : (n : ℕ) → digits (succ n) ≡ succ (digits (half (succ n)))
  lemma-digits n = {!!} -- refl (digits (succ n))

  data G : ℕ → ℕ → Set where
    -- naive definition: "digits zero ≡ zero"
    base : G zero zero

    -- naive definition: "digits (succ n) ≡ succ (digits (half (succ n)))"
    step : {n y : ℕ} → G (half (succ n)) y → G (succ n) (succ y)

  lemma-G-is-functional : (a b b' : ℕ) → G a b' → b ≡ b'
  lemma-G-is-functional = {!!}

  data Σ (X : Set) (Y : X → Set) : Set where
    _,_ : (x : X) → Y x → Σ X Y

  lemma-G-is-total : (a : ℕ) → Σ ℕ (G a)
  lemma-G-is-total a = {!!} , {!!}

  lemma-G-is-computed-by-function : (a : ℕ) → G a (digits a)
  lemma-G-is-computed-by-function a = {!!}
