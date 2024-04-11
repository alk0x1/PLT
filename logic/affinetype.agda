open import Data.Bool using (Bool; true; false; _∧_; not)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List using (List; []; _∷_)

data Term : Set where
    Var : ℕ -> Term
    Lam : Term -> Term
    App : Term -> Term -> Term



isAffine : Term -> Bool
isAffine term = isAffine' term []
  where
    isAffine' : Term -> List ℕ -> Bool
    isAffine' (Var x) vars = not (x ∈ vars)
    isAffine' (Lam body) vars = isAffine' body vars
    isAffine' (App f a) vars = isAffine' f vars _∧_ isAffine' a vars


norm : Term -> Term
norm (Var x) = Var x
norm (Lam body) = Lam (norm body)
norm (App (Lam body) arg) = norm (substitute body 0 (norm arg))
norm (App f a) = App (norm f) (norm a)

normalize : Term -> Maybe Term
normalize term with isAffine term
... | true = just (norm term)
... | false = nothing