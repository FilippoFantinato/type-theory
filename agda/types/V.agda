module types.V where

data V : Set₁ where
  sup : {I : Set} → (I → V) → V

