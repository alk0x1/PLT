module first_order_dependent_types where

open import Data.String
open import Data.List
open import Data.Product
open import Data.Maybe
open import Relation.Binary.PropositionalEquality -- for propositional equality


data Term : Set where
  var : String → Term
  abs : String → Term → Term
  app : Term → Term → Term
 
data Type : Set where
  typeVar : String -> Type
  depProd : String -> Type -> Type -> Type
  typeApp : Type -> Type -> Type


data Kind : Set where
  star : Kind
  typeFamilies : String -> Type -> Kind -> Kind



Context : Set
Context = List (String × Type)

addBinding : String -> Type -> Context -> Context
addBinding v t ctx = (v , t) ∷ ctx

lookupContext : String → Context → Maybe Type
lookupContext _ [] = nothing
