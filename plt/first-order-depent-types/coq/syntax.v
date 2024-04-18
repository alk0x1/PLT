Require Import List.
Import ListNotations.
Require Import String.
Require Import Bool.


Inductive Term : Type :=
  | var : string -> Term
  | abs : string -> Term -> Term
  | app : Term -> Term -> Term.


Inductive TypeExpr : Set :=
  | typeVar : string -> TypeExpr
  | depProd : string -> TypeExpr -> TypeExpr -> TypeExpr
  | typeApp : TypeExpr -> TypeExpr -> TypeExpr.

Inductive Kind : Set :=
  | star : Kind
  | typeFamily : string -> TypeExpr -> Kind -> Kind.

(* Context Definitions *)
Inductive Binding :=
  | TypeBinding : string -> TypeExpr -> Binding
  | KindBinding : string -> Kind -> Binding.

Definition Context := list Binding.

Definition addTypeBinding (name : string) (t : TypeExpr) (ctx : Context) : Context :=
  (TypeBinding name t) :: ctx.
Definition addKindBinding (name : string) (K : Kind) (ctx : Context) : Context :=
  (KindBinding name K) :: ctx.


Fixpoint lookupType (key : string) (ctx : Context) : option TypeExpr :=
  match ctx with
  | [] => None
  | TypeBinding v t :: ctx' => if String.eqb key v then Some t else lookupType key ctx'
  | KindBinding _ _ :: ctx' => lookupType key ctx'
  end.

Fixpoint lookupKind (key : string) (ctx : Context) : option Kind :=
  match ctx with
  | [] => None
  | TypeBinding _ _ :: ctx' => lookupKind key ctx'
  | KindBinding v k :: ctx' => if String.eqb key v then Some k else lookupKind key ctx'
  end.
