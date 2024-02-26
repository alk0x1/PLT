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

  -- commutativity we want to show that m + n ≡ n + m
  -- Lemmas zero + n ≡ n; m + zero ≡ m
  +-identity : ∀ (m : Nat) -> m + zero ≡ m
  +-identity zero = 
    begin
      zero + zero
    ≡⟨⟩
      zero
    ∎
  +-identity (succ m ) = 
    begin
      succ m + zero
    ≡⟨⟩
      succ (m + zero)
    ≡⟨ cong succ (+-identity m) ⟩
      succ m
    ∎

  --  m + suc n ≡ suc (m + n)
  +-succ : ∀ (m n : Nat) → m + succ n ≡ succ (m + n)
  +-succ zero n =
    begin
      zero + succ n
    ≡⟨⟩
      succ n
    ≡⟨⟩
      succ (zero + n)
    ∎
  +-succ (succ m) n =
    begin
      succ m + succ n
    ≡⟨⟩
      succ (m + succ n)
    ≡⟨ cong succ (+-succ m n) ⟩
      succ (succ (m + n))
    ≡⟨⟩
      succ (succ m + n)
    ∎

  +-comm : ∀ (m n : Nat) → m + n ≡ n + m
  +-comm m zero =
    begin
      m + zero
    ≡⟨ +-identity m ⟩
      m
    ≡⟨⟩
      zero + m
    ∎
  +-comm m (succ n) =
    begin
      m + succ n
    ≡⟨ +-succ m n ⟩
      succ (m + n)
    ≡⟨ cong succ (+-comm m n) ⟩
      succ (n + m)
    ≡⟨⟩
      succ n + m
    ∎