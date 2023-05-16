module types.binary-tree where


data BinaryTree (A : Set) : Set where
  nil : BinaryTree A
  fork : A → BinaryTree A → BinaryTree A → BinaryTree A
