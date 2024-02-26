data Bool : Set where
  true : Bool
  false : Bool

  
not : Bool -> Bool
not true = false
not false = true


equiv : Bool -> Bool -> Bool
equiv true true = true
equiv true false = false
equiv false true = false
equiv false false = true

_||_ : Bool -> Bool -> Bool
true || _ = true
_ || true = true
_ || _ = false

_&&_ : Bool -> Bool -> Bool
true && true = true
_ && _ = false


_=>_ : Bool -> Bool -> Bool
true => false = false
true => true = true
false => true = true
false => false = true
