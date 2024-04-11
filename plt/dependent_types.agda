data Nat : Set where
  zero : Nat
  succ : Nat → Nat

data Vec (A : Set) : Nat → Set where
  []  : Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (succ n)
-- init : Πn:Nat. data → Vector n

-- init : ∀ {A : Set} → (n : Nat) → A → Vec A n
-- init zero    v = []
-- init (succ n) v = v ∷ init n

init : ∀ {A : Set} (n : Nat) (v : A) → Vec A n
init zero v = []
init (succ n) v = v ∷ init n v

