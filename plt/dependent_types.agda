module dependent_types where

-- Π-types (Dependent Product Types) ∀
-- - type of the output can depend on the actual input value passed to the function. 
-- - Π(x:A)→B(x), Here B depends on x
-- - defining functions and ensuring that operations can be performed safely under all conditions specified by the input
-- Σ-types (Dependent Sum Types) ∃
-- - type of the second component of the pair can depend on the value of the first component
-- - Σ(x:A)×B(x), Here we have a pair where the element of type B(x) vary depending on x.
-- - representing data structures and states where one part of the structure or state may determine the characteristics of another part

module VecExample where
  data Nat : Set where
    zero : Nat
    succ : Nat → Nat

  data Vec (A : Set) : Nat → Set where
    []  : Vec A zero
    _∷_ : ∀ {n} → A → Vec A n → Vec A (succ n)
  infixr 5 _∷_

  -- Initialize a vector of length n with all elements set to v.
  init : ∀ {A : Set} (n : Nat) (v : A) → Vec A n
  init zero    v = []
  init (succ n) v = v ∷ init n v

  one : Nat
  one = succ zero
  two : Nat
  two = succ one
  three : Nat
  three = succ two
  five : Nat
  five = succ (succ three)

  exampleVec : Vec Nat three
  exampleVec = init three five

  -- Construct a vector by prepending an element.
  cons : ∀ {A : Set} {n : Nat} → A → Vec A n → Vec A (succ n)
  cons e v = e ∷ v

  exampleVec3 : Vec Nat three
  exampleVec3 = one ∷ two ∷ three ∷ []

  exampleVector : Vec Nat three
  exampleVector = cons three (cons two (cons one []))

  first : ∀ {A : Set} {n : Nat} -> Vec A (succ n) -> A
  first (x ∷ _) = x

  exampleVecx : Vec Nat three
  exampleVecx = one ∷ two ∷ three ∷ []
  exampleFirst : Nat
  exampleFirst = first exampleVecx

-- Axiom Choice
-- if for every element a of a type A there exists an element b of B such that P(a,b) 
-- then there exists a function f mapping an arbitrary x:A to an element of B such that P(x, f x)
module AxiomOfChoice where

  open import Data.Product
  open import Relation.Nullary
  open import Relation.Binary.PropositionalEquality
  open import Data.Empty  -- Import for bottom type (⊥)

  A : Set₂
  A = Set₁

  B : A → Set₁
  B a = Set

  P : (a : A) → B a → Set₁
  P a b = ¬ (b ≡ ⊥)

  axiomOfChoice : (∀ a → Σ (B a) (λ b → P a b)) → Σ ((a : A) → B a) (λ f → ∀ a → P a (f a))
  axiomOfChoice h = ((λ a → let (b , _) = h a in b) , (λ a → let (_ , p) = h a in p))

module PullbackExample where
  open import Data.Product
  open import Relation.Binary.PropositionalEquality
  open import Data.Nat

  A : Set
  A = ℕ

  B : Set
  B = ℕ

  C : Set
  C = ℕ

  f : A → C
  f a = a + 1

  g : B → C
  g b = b * 2

  Pullback : Set
  Pullback = Σ (A × B) λ ab → f (proj₁ ab) ≡ g (proj₂ ab)

