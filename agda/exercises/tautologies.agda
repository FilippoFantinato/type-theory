{-#OPTIONS #-}

module exercises.tautologies where

open import types.natural-numbers
open import types.positive
open import types.equality
open import types.empty
open import types.sum
open import types.times
open import types.decidable

module _
  {A B : Set}
  where

  -- EXERCISE: A × B → B × A
  lemma-×-commutative : A × B → B × A
  lemma-×-commutative (x , y) = (y , x)

  dni : {A : Set} → A → ¬ (¬ A)
  dni ¬ p = {!!}

  contraposition : (A → B) → (¬ B → ¬ A)
  contraposition f = {!!} 
  
  de-morgan₁ : (¬ (A ⊎ B)) → (¬ A) × (¬ B)
  de-morgan₁ f = (g , (λ y → f (right y)))
    where
    g : ¬ A
    g x = f (left x)

  de-morgan₂ : (¬ A) × (¬ B) → ¬ (A ⊎ B)
  de-morgan₂ = {!!}

  de-morgan₃ : (¬ A) ⊎ (¬ B) → ¬ (A × B)
  de-morgan₃ = {!!}

  -- No from negative information to positive information,
  -- since that is not constructive
  de-morgan₄ : ¬ (A × B) → (¬ A) ⊎ (¬ B)
  de-morgan₄ = {!!}

  -- Law of excluded middle (LEM) : A ∨ ¬A, cannot be formalized since it's actually too big that set
  witnesses-of-LEM : Set₁
  witnesses-of-LEM = (A : Set) → (A ⊎ (¬ A))

  this-hole-cannot-be-filled : witnesses-of-LEM
  this-hole-cannot-be-filled = {!!}


  postulate
    oracle : witnesses-of-LEM
    lol    : ⊥

  not-it-can-be-filled : witnesses-of-LEM
  not-it-can-be-filled = oracle

  positivity-is-decidable : (a : ℕ) → Dec (Positive a)
  positivity-is-decidable zero     = no (λ ())
  positivity-is-decidable (succ a) = yes (positive-succ a)


  -- Every inhabited set of natural numbers conrains a minimum
  -- We can picture a function P : ℕ → Set as a set of natural numbers
  -- Namely, P n is the type of witnesses that n belongs to the set

  -- The following holes cannot be filled
  -- minimum : (P : ℕ → Set) → (a₀ : ℕ) → P a₀ → ℕ
  -- minimum = {!!}

  -- lemma-minimum-is-computed-correctly : (P : ℕ → Set) → (a₀ : ℕ) → (p : P a₀) → (n : ℕ) → P n → minimum P a₀ p ≦ n
  -- lemma-minimum-is-computed-correctly = {!!}


  -- Constructive substitute 1 for the principle that every inhabited set has a mininum
  module _ (P : ℕ → Set) (oracle : (n : ℕ) → Dec (P n)) where

    data _≦_ : ℕ → ℕ → Set where

    minimum : (a₀ : ℕ) → P a₀ → ℕ
    minimum = {!!}

    lemma-minimum-is-computed-correctly
      : (a₀ : ℕ) → (p : P a₀) → (n : ℕ) → P n → minimum a₀ p ≦ n
    lemma-minimum-is-computed-correctly = {!!}

