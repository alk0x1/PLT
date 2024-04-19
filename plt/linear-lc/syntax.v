(* Linear type systems ensure that every variable is used exactly once by
allowing exchange but not weakening or contraction. *)

(* Γ1 , x1 :T1 , x2 :T2 , Γ2 ` t : T -> Γ1 , x2 :T2 , x1 :T1 , Γ2 ` t : T *)
Require Import String.


Inductive Qualifier : Type :=
	| lin : Qualifier
	| un : Qualifier.

Inductive Term : Type :=
	| var : string -> Term
	| boolean : Qualifier -> bool -> Term
	| condition: Term -> Term -> Term -> Term
	| pr : Qualifier -> Term -> Term -> Term
	| abs : string -> Term -> Term
	| splt : Term -> string -> string -> Term -> Term.

Inductive Pretype : Type :=
  | BoolType : Pretype
  | PairType : Pretype -> Pretype -> Pretype
  | FuncType : Pretype -> Pretype -> Pretype.

Inductive Ty : Type :=
  | QualType : Qualifier -> Pretype -> Ty.

Inductive Context : Type :=
  | empty_context : Context
  | extend_context : Context -> string -> Ty -> Context.