infixr 5 _∷_

data Nat : Set where
  zero : Nat
  succ : Nat → Nat

data Vec (A : Set) : Nat → Set where
  []  : Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (succ n)

-- {Length} n : Nat 
-- {Value}  A : Data
-- init : Πn:Nat. data → Vector n
init : ∀ {A : Set} (n : Nat) (v : A) → Vec A n
init zero v = []
init (succ n) v = v ∷ init n v

one : Nat
one = succ zero
two : Nat
two = succ (succ zero)
three : Nat
three = succ (succ (succ zero))
five : Nat
five = succ (succ (succ (succ (succ zero))))

exampleVec : Vec Nat three
exampleVec = init three five

-- cons : Πn:Nat. data → Vector n → Vector (n+1).
-- cons : ∀ {A: Set} (n: Nat) (e: A) (v : Vec) -> Vec A n v
cons : ∀ {A : Set} {n : Nat} → A → Vec A n → Vec A (succ n)
cons e v = e ∷ v

exampleVec3 : Vec Nat three
exampleVec3 = one ∷ two ∷ three ∷ []

exampleVector : Vec Nat three
exampleVector = cons three (cons two (cons one []))

-- first : Πn:Nat.Vector(n+1) → data
first : ∀ {A : Set} {n : Nat} -> Vec A (succ n) -> A
first (x ∷ _) = x
 
exampleVecx : Vec Nat three
exampleVecx = one ∷ two ∷ three ∷ []
exampleFirst : Nat
exampleFirst = first exampleVec