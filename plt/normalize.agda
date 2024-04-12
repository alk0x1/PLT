module normalize where
import PLFA.Foo

open import Data.Nat

sumTo : ℕ → ℕ
sumTo 0 = 0
sumTo n = n + sumTo (n ∸ 1)
