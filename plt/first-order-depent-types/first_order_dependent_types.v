Require Import List.
Import ListNotations.
Require Import String.
Require Import Bool.

(* Syntax (BNF) *)

Inductive Term : Type :=
  | var : string -> Term
  | abs : string -> Term -> Term
  | app : Term -> Term -> Term.

Check var "x".
Check abs "x" (var "x").
Check app (var "x") (var "y"). 



Inductive TypeExpr : Set :=
  | typeVar : string -> TypeExpr
  | depProd : string -> TypeExpr -> TypeExpr -> TypeExpr
  | typeApp : TypeExpr -> TypeExpr -> TypeExpr.

Inductive Kind : Set :=
  | star : Kind
  | typeFamily : string -> TypeExpr -> Kind ->Kind.

Definition Context := list (string * TypeExpr).

Definition addBinding (v : string) (t : TypeExpr) (ctx : Context) : Context :=
  (v, t) :: ctx.

Fixpoint lookupContext (key : string) (ctx : Context) : option TypeExpr :=
  match ctx with
  | [] => None
  | (v, t) :: ctx' =>
    if String.eqb key v then Some t
    else lookupContext key ctx'
  end.


Example test_lookup_added : lookupContext "x" (addBinding "x" (typeVar "int") []) = Some (typeVar "int").
Proof.
  simpl.
  reflexivity.
Qed.

Example test_lookup_nonexistent : lookupContext "y" [] = None.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_lookup_old_binding : lookupContext "x" (addBinding "y" (typeVar "bool") (addBinding "x" (typeVar "int") [])) = Some (typeVar "int").
Proof.
  simpl.
  reflexivity.
Qed.