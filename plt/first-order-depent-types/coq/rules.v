Require Import syntax.
Require Import String.
Require Import List.
Import ListNotations.

(* Well-formed Kinds (WF) *)

Inductive WellFormedType : Context -> TypeExpr -> Kind -> Prop :=
  (* Definitions for well-formed types go here, including a case for type variables: *)
  | WfTypeVar : forall ctx X,
      (exists K, lookupKind X ctx = Some K) ->  (* Checks if X is a kind variable in the context *)
      WellFormedType ctx (typeVar X) star.
  (* ... other cases for well-formed types ... *)

Inductive WellFormedKind : Context -> Kind -> Prop :=
	| WfStar : forall ctx, WellFormedKind ctx star
	| WfPi : forall ctx X T K,
		WellFormedType ctx T star ->
		WellFormedKind (addTypeBinding X T ctx) K ->
		WellFormedKind ctx (typeFamily X T K).