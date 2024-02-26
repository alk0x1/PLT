module Quantifiers where
  open import Isomorphism using (_≃_; extensionality; ∀-extensionality)
  open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
  open import Function using (_∘_)
  

  postulate
    -- show that 
    ∀-distrib-× : ∀ {A : Set} 
      {B C : A → Set} → (∀ (x : A) → B x × C x) 
      ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
