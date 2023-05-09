module types.times where


-- Both A and B are inhabited
data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

