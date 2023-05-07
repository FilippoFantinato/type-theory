module types.booleans where

data Bool : Set where
  true  : Bool
  false : Bool

-- Negation
!_ : Bool → Bool
! true = false
! false = true

-- AND
_&&_ : Bool → Bool → Bool
_&&_ true y = y
_&&_ false y = false

-- OR
_||_ : Bool → Bool → Bool
_||_ true y  = true
_||_ false y = y

