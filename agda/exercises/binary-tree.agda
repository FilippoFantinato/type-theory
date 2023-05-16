module exercises.binary-tree where

open import types.binary-tree

exampleBinaryTree : {A : Set} → A → A → A → BinaryTree A
exampleBinaryTree x y a = fork x nil (fork y (fork a nil nil)  nil)

