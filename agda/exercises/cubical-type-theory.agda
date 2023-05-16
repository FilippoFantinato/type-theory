{-# OPTIONS --cubical #-}

module exercises.cubical-type-theory where
  {-
    Homotopy theory: Types as animas

    -- An anima is a space considered up to homotopy equivalence

    A dictionary:
    Logic                  Type Theory          Homotopy Theory
    prop.                  type                 anima
    witness                x : X                point of an anima
    contradiction          ⊥(empty type)       Empty anima
    statement that x=y     (x ≡ y)              anima of path from x to y
    trivial proof that x=x  relf : x ≡ x        trivial path from x to x
  -}

  open import Cubical.Core.Everything

  data S¹ : Type where
    north : S¹
    loop : north ≡ north
    -- without loop, we automatically have refl : north ≡ north
    -- but loop is a distinct path from north to north.
    -- loop · loop , loop · loop · loop , ...
    -- sym loop , sym loop · sym loop , ...
    -- In fact, the type (north ≡ north) is equivalent to ℤ

  data UnitInterval : Type where
    start : UnitInterval
    end   : UnitInterval
    seg   : start ≡ end

  --      --
  --     /  \
  --     *  *
  --     \  /‌‌‌
  --      --
  data Diamond : Type where
    start : Diamond
    end   : Diamond
    upper : start ≡ end
    lower : start ≡ end

  open import Data.Nat
  data ℤ : Type where
    _⊖_ : ℕ → ℕ → ℤ
    step : (a b : ℕ) → a ⊖ b ≡ (suc a) ⊖ (suc b)

  -- 0ℤ = 0 ⊖ 0 = 5 ⊖ 5
  -- 1ℤ = 1 ⊖ 0 = 6 ⊖ 5

  add1 : ℤ → ℤ
  add1 (a ⊖ b)   = suc a ⊖ b
  add1 (step a b i) = step (suc a) b i
  -- path from (a ⊖ b) to (suc a ⊖ suc b)

  refl' : {A : Type} → {x : A} → x ≡ x
  refl' {A} {x} = λ i → x
  -- In cubical Agda/Cubical type theory
  -- (x ≡ y) is the type of functions y from I to A
  -- such that Y i0 is definitionally the same as x
  -- and such that Y i1 is definitionally the same as y

  -- The picture of I is is the unit interval: *-----*
  --                                           i0    i1


  symm' : {A : Type} {x y : A} → x ≡ y → y ≡ x
  symm' p = λ i → p (~ i)

  funext : {A B : Type} {f g : A → B} → ((x : A) → f x ≡ g x) → f ≡ g
  funext h = λ i → λ x → h x i

  data ℤ/3 : Type where
    zero : ℤ/3
    succ : ℤ/3 → ℤ/3
    -- * * * * * * * * *  Our type so far
    pa   : zero ≡ (succ (succ (succ zero)))

  {-
    wont-work : ℤ/3 → ℕ
    wont-work zero = zero
    wont-work (succ x) = suc (wont-work x)
    wont-work (pa i) = {!!} -- I cannot fill this hole, because there is no path
  -}

  {-
    foo : Type → ℤ
    foo ⊥ = {!!}
    foo ℕ = {!!}
    foo (A × B) = ?
    foo (A → B) = ?
    -- foo = ?
  -}

  
