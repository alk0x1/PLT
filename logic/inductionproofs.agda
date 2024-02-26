module InductionProofs where
  open import NatNumbers using (Nat; _+_; _*_; _-_; _^_; zero; succ)

  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; cong; sym)
  open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

  m : Nat
  m = succ zero
  n : Nat
  n = succ(succ zero)

-- associativity:  we want to show that (m + n) + p ≡ m + (n + p)
  +-assoc : ∀ (m n p : Nat) → (m + n) + p ≡ m + (n + p)
  -- basis case
  +-assoc zero n p = 
    begin
      (zero + n) + p
    ≡⟨⟩ 
      n + p
    ≡⟨⟩
      zero + (n + p)
    ∎

  +-assoc (succ m) n p =
    begin
      (succ m + n) + p
    ≡⟨⟩
      succ (m + n) + p
    ≡⟨⟩
      succ ((m + n) + p)
      -- cong applies the "succ" function to both sides of an equation, maintaining equality.
    ≡⟨ cong succ (+-assoc m n p) ⟩
      succ (m + (n + p))
    ≡⟨⟩
      succ m + (n + p)
    ∎
