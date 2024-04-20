Require Import syntax.

Lemma concat_empty_l : forall (ctx : Context),
  context_concat empty_context ctx = ctx.
Proof.
  intros ctx.
  simpl.
  reflexivity.
Qed.

Lemma concat_empty_r : forall (ctx : Context),
  context_concat ctx empty_context = ctx.
Proof.
  intros ctx.
  induction ctx as [|rest x ty IH].
  - simpl. reflexivity.
  - simpl. rewrite x. reflexivity.
Qed.
