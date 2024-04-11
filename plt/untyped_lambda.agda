open import Data.Bool using (Bool; true; false; T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _×_)
open import Data.String using (String; _≟_)
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (False; toWitnessFalse)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

-- BNF
-- <expression> ::= <variable>
--                | <abstraction>
--                | <application>

-- <variable> ::= [a-zA-Z]+
-- <abstraction> ::= "λ" <variable> "." <expression>
-- <application> ::= "(" <expression> <expression> ")"

Id : Set
Id = String

infix  5  ƛ_⇒_
infixl 7  _·_
infix  9  `_

data Expr : Set where
  Var : String -> Expr          -- Variables
  Abs : String -> Expr -> Expr  -- Abstraction (λx.E)
  App : Expr -> Expr -> Expr


id : Expr
id = Abs "x" (Var "x")

appId : Expr
appId = App id id

-- two : Expr
-- two = Abs "f" (Abs "x" (App (Var "f") (App (Var "f") (Var "x"))))

data Term : Set where
  `_    :  Id → Term
  ƛ_⇒_  :  Id → Term → Term
  _·_   : Term → Term → Term


one : Term
one = ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · ` "z"
two : Term
two = ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")
three : Term
three = ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · (` "s" · ` "z"))

add : Term -> Term -> Term
add m n = ƛ "s" ⇒ ƛ "z" ⇒ (m · ` "s") · (n · ` "s" · ` "z")

normalize : Term -> Term
normalize = {!!}  -- Complex implementation goes here
