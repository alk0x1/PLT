module Quantifiers where
  open import Isomorphism using (_≃_; extensionality; ∀-extensionality)
  open import Function using (_∘_)
  
  +-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
