module exercises.function-extensionality where

open import types.natural-numbers
open import types.equality

module Experiment where
  pred' : ℕ → ℕ
  pred' = pred

  _ : pred ≡ pred'
  _ = refl _

  pred'' : ℕ → ℕ
  pred'' zero     = zero
  pred'' (succ n) = n

  -- NOTE: There is no way to fill this hole
  _ : pred ≡ pred''
  _ = {!!}

  lemma : (n : ℕ) → pred n ≡ pred'' n
  lemma zero     = refl zero
  lemma (succ n) = refl _


  -- Ordinary blackboard mathematics employs the following axiom:
  -- FUNCTION EXTENSIONALITY: functions which are pointwise equal are equal

  postulate
    funext : {A B : Set} {f g : A → B} → ((x : A) → (f x) ≡ (g x)) → f ≡ g


  theorem : pred ≡ pred''
  theorem = funext lemma

  -- In case you need function extensionality, you can just postulate it.
  -- However note that this will destroy canonicity
  -- Canonicity is the property that every terms of type ℕ reduces to a numeral
  -- (to a term of the form (succ (succ ... (zero)...)))
  -- More generally, canonicity is the property that every term of evrey
  -- inductively generated type reduces to a form ehich begins with one of the constractors


module Fail where
  data ℤ : Set where
    inj : ℕ → ℤ -- injection
    neg : ℕ → ℤ

  add : ℤ → ℤ → ℤ
  add (inj x) (inj y) = inj (x + y)
  add (inj x) (neg y) = {!!}
  add (neg x) (inj y) = {!!}
  add (neg x) (neg y) = neg (succ (x + y))


module Quotient
  (A : Set)
  (_∼_ : A → A → Set)
  (isEquivalence : {!!}) where

  postulate
    Q : Set
    [_]   : A → Q -- intuitively, [ x ] should be the equivalence class of x
    eq    : {x y : A} → x ∼ y → [ x ] ≡ [ y ]
    exact : {x y : A} → [ x ] ≡ [ y ] → x ∼ y
    rec   : {B : Set} (f : A → B) → ((x y : A) → x ∼ y → (f x) ≡ (f y)) → (Q → B)
    comp  : {B : Set} (f : A → B) → (ext : ((x y : A) → x ∼ y → (f x) ≡ (f y))) {x : A} → rec f ext ([ x ]) ≡ (f x)
    -- This is the recursor and its computation rule
    -- We also need the induction principle and the computation for that.
    -- In fact, the induction principle and its computation rule render the recursor and its rule superfluous

module PreIntegers where
  open import types.times

  -- The type pre-integers (representations of integers
  ℤ = ℕ × ℕ

  add : ℤ → ℤ → ℤ
  add (a , b) (a' , b') = (a + a') , (b + b')
  -- Informally: (a-b) + (a-b) = (a+a') - (b+b')

  -- "x ≈ y" should be the type of witnesses that the two pre-integers x and y
  -- denote the same integer
  _≈_ : ℤ → ℤ → Set
  (a , b) ≈ (a' , b') = (b' + a) ≡ (a' + b)

  _ : (zero , zero) ≈ (succ zero , succ zero)
  _ = refl _

  -- The true type of integers would be the quotient of ℤ by the equivalence relation ≈
  -- so the values of the true type ℤ of integers would be equivalence classes [ x ]
  -- such that [ x ] ≈ [ y ] ⇔ x = y

  -- ISSUE: in agda, we don't have quotients
  -- There is no keyword "quotient" like ℤ = quotient ℤ ≈


module Integers where
  open import types.times
  open Quotient PreIntegers.ℤ PreIntegers._≈_ {!!}

  ℤ : Set
  ℤ = Q

  integer-zero : ℤ
  integer-zero = [ (zero , zero) ]

  integer-minus-one : ℤ
  integer-minus-one = [ (zero , succ zero) ]


record isEquivalence {X : Set} (_∼_ : X → X → Set) : Set where
  field
    reflexive  : (x : X) → x ∼ x
    symmetric  : {x y : X} → x ∼ y → y ∼ x
    transitive : {x y z : X} → x ∼ y → y ∼ x → x ∼ z

lemma-≈-is-equivalence-relation : isEquivalence PreIntegers._≈_
lemma-≈-is-equivalence-relation = record {
  reflexive = {!!} ;
  symmetric = {!!} ;
  transitive = {!!} }


-- SETOID HELL
module Setoids where
  open import types.times
  -- A setoid is a type together with an equivalence relation on it.
  -- For instance, the type ℤ of pre-inetegrs together with _≈_ is a setoid.

  -- Fucntions between setoids are functions between the underlying types
  -- which respects the given equivalence relations

  record Setoid : Set₁ where
    field
      Carrier : Set
      _∼_     : Carrier → Carrier → Set
      isEquiv : isEquivalence _∼_


  ℤ' : Setoid
  ℤ' = record {
    Carrier = PreIntegers.ℤ ;
    _∼_     = PreIntegers._≈_;
    isEquiv = lemma-≈-is-equivalence-relation }

  record _⇒_ (X Y : Setoid) : Set where
    field
      fun : Setoid.Carrier X → Setoid.Carrier Y
      track : {x x' : Setoid.Carrier X} → Setoid._∼_ X x x' → Setoid._∼_ Y (fun x) (fun x')

  negation : ℤ' ⇒ ℤ'
  negation = record {
    fun = λ { (a , b) → (b , a) } ;
    track = {!!} }
