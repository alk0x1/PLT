module lambda where
  module combinators where
    K : (A B : Set) -> A -> B -> A
    K_ _x _ = x
    S : (A B C : Set) -> (A -> B -> C) -> (A -> B) -> A -> C
    S _ _ _ f g x = f x (g x)