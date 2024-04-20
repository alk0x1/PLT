(* Linear type systems ensure that every variable is used exactly once by
allowing exchange but not weakening or contraction. *)

(* Γ1 , x1 :T1 , x2 :T2 , Γ2 ` t : T -> Γ1 , x2 :T2 , x1 :T1 , Γ2 ` t : T *)
Require Import String.
Require Import List.
Import ListNotations.

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

Fixpoint context_concat (ctx1 ctx2 : Context) : Context :=
  match ctx1 with
  | empty_context => ctx2
  | extend_context rest x ty => 
      extend_context (context_concat rest ctx2) x ty
  end.

Definition example_ctx1 : Context :=
  extend_context (extend_context empty_context "x" (QualType lin BoolType)) "y" (QualType un BoolType).

Definition example_ctx2 : Context :=
  extend_context empty_context "z" (QualType lin BoolType).

Definition example_ctx_concatenated : Context :=
  context_concat example_ctx1 example_ctx2.


Definition is_empty_ctx (ctx : Context) : bool :=
  match ctx with
  | empty_context => true
  | _ => false
  end.

(* Inductive definition for context splitting *)
Inductive split_context : Context -> Context -> Context -> Prop :=
  | M_empty : split_context empty_context empty_context empty_context.