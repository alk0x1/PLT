## First-order dependent types (λLF)

### Syntax (BNF)
|t ::=    |                  |terms:           |
|---------|------------------|-----------------|
|         | x                | variable        |
|         | λx:T.t           | abstraction     |
|         | t t              | application     |


|  T ::=  |                  |types:					         |
|---------|------------------|-------------------------|
|   			| X                | type/family variable 	 |
|         | Πx:T.T           | dependent product type  |
|         | T t              | type family application |

|K ::=    |                  |kinds:      		       |
|---------|------------------|-----------------------|
|         | *                | kind of proper types  |
|         | Πx:T.K           | kind of type families |


| Γ ::= |                	    | contexts:|
|-----------|---------------- |------------------------|
|           | ∅              | empty context   |
|           | Γ, x:T          | term variable binding |
|           | Γ, X::K         | type variable binding |

### Kinding										[Γ ⊢ T :: K]

X :: K ∈ Γ  
Γ ⊢ K  
───────────── (K-Var)  
Γ ⊢ X :: K


Γ ⊢ T₁ :: *  
Γ, x:T₁ ⊢ T₂ :: *  
──────────────────── (K-Pi)  
Γ ⊢ Πx:T₁.T₂ :: *


Γ ⊢ S :: Πx:T.K  
Γ ⊢ t : T  
───────────── (K-App)  
Γ ⊢ S t : [x ↦ t]K

Γ ⊢ T :: K  
Γ ⊢ K ≡ K'  
───────────── (K-Conv)  
Γ ⊢ T :: K'

### Typing 									[Γ ⊢ t : T]
x : T ∈ Γ  
Γ ⊢ T :: *  
───────────── (T-Var)  
Γ ⊢ x : T

Γ ⊢ S::*  
Γ, x:S ⊢ t:T  
───────────── (T-Abs)  
Γ ⊢ λx:S.t : Πx:S.T

Γ ⊢ t₁ : Πx:S.T  
Γ ⊢ t₂ : S  
───────────── (T-App)  
Γ ⊢ t₁ t₂ : [x ↦ t₂]T

Γ ⊢ t:T  
Γ ⊢ T ≡ T' :: *  
───────────── (T-Conv)  
Γ ⊢ t: T'


## First-order dependent types (λLF)—Equivalence rules
Γ ⊢ T₁ ≡ T₂ :: * forall