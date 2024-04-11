data Affine : Set where
  dups {a : Set} (x : a)

open import Agda.Prop

Set Prop = forall {p : *} -> Prop p

-- Dependent function type with affine constraint
data AffineFun {A B : Set} (f : A -> B) : Set where
  aff_fun : @forall (a : A) (x : dups a), B

data Normalize {A : Set} : A -> Set where
  norm : @forall (a : A), Normalize a

open import Agda.Contraction

-- Rule for variables (no change)
norm (dups a x) : Normalize (dups a x) = ,

-- Rule for function application (replace with your specific function)
norm (@aff_fun f .@ b x) : Normalize (MyFun f (norm x)) = ... -- Implement function normalization here

-- Example function (replace with your actual function)
data MyFun {A B : Set} (f : A -> B) : Set where
  my_fun : @forall (a : A), MyFun f a

-- Function application normalization with (potential) error handling
norm (@MyFun f .@ b x) : Normalize (MyFun f (norm x)) =
  case norm x of
    -- Handle successful normalization
    | ... -> ...
    -- Handle potential errors (e.g., invalid term structure)
    | _ -> error "Invalid term structure for MyFun"
