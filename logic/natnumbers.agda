
module NatNumbers where
  data Bool : Set where
    true : Bool
    false : Bool

  data Nat : Set where
    zero : Nat
    succ : Nat -> Nat

  pred : Nat -> Nat
  pred zero = zero
  pred (succ n) = n

  _+_ : Nat -> Nat -> Nat
  zero + m = m
  (succ n) + m = succ (n + m)

  _-_ : Nat -> Nat -> Nat
  zero - succ n = zero
  m - zero = m
  succ m - succ n = m - n
  
  _*_ : Nat -> Nat -> Nat
  zero * n = zero
  succ n * m = (n * m) + m

  _^_ : Nat -> Nat -> Nat
  zero ^ _ = zero
  _ ^ zero = succ zero
  succ m ^ succ n = (succ m ^ n) * succ m

  _<_ : Nat -> Nat -> Bool
  zero < zero = false
  zero < succ n = true
  succ n < zero = false
  succ n < succ m = n < m

  _>_ : Nat -> Nat -> Bool
  zero > zero = false
  zero > succ n = false
  succ n > zero = true
  succ n > succ m = n > m

  _<=_ : Nat -> Nat -> Bool
  zero <= zero = true
  zero <= succ n = true
  succ n <= zero = false
  succ n <= succ m = n < m

  _>=_ : Nat -> Nat -> Bool
  zero >= zero = true
  zero >= succ n = false
  succ n >= zero = true
  succ n >= succ m = n >= m

  infixl 6  _+_  _-_
  infixl 7  _*_

  open import Relation.Binary.PropositionalEquality using (_≡_; refl)

  one : Nat
  one = succ zero

  two : Nat
  two = succ one
  three : Nat
  three = succ two
  eight : Nat
  eight = succ (succ (succ (succ (succ three))))

  plusOneOneIsTwo : one + one ≡ two
  plusOneOneIsTwo = refl

  timesOneOneIsOne : one * one ≡ one
  timesOneOneIsOne = refl
  timesTwoThreeIsSix : two * three ≡ succ (succ (succ  three))
  timesTwoThreeIsSix = refl

  minusOneOneIsZero : one - one ≡ zero
  minusOneOneIsZero = refl
  minusOneTwoIsOne : two - one ≡ one
  minusOneTwoIsOne = refl 

  oneLessThenTwo : one < two ≡ true
  oneLessThenTwo = refl
  twoLessThenOne : two < one ≡ false
  twoLessThenOne = refl

  oneGreaterThenTwo : one > two ≡ false
  oneGreaterThenTwo = refl
  twoGreaterThenOne : two > one ≡ true
  twoGreaterThenOne = refl

  oneLessOrEqualThenTwo : one <= two ≡ true
  oneLessOrEqualThenTwo = refl
  twoLessOrEqualThenOne : two <= one ≡ false
  twoLessOrEqualThenOne = refl
  
  oneGreaterOrEqualThenTwo : one <= two ≡ true
  oneGreaterOrEqualThenTwo = refl
    
  twoToThreePowerEqualEight : two ^ three ≡ eight
  twoToThreePowerEqualEight = refl  