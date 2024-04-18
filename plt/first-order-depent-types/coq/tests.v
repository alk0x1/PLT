Require Import syntax.
Require Import List.
Import ListNotations.
Require Import String.


Check var "x".
Check abs "x" (var "x").
(* Check app (var "x") (var "y"). *)

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
