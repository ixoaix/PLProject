Require Import Reals ssreflect.

Module Rsimpl.

Local Open Scope R.

Lemma compute_1: forall (k : nat) (len : nat),
  -2 * PI * 0 * INR k * / INR len = 0.
Proof.
  intros.
  pose proof Rmult_0_r (-2 * PI).
  rewrite H.
  pose proof Rmult_0_l (INR k * / INR len).
  pose proof Rmult_assoc 0 (INR k) (/ INR len).
  rewrite <- H1 in H0.
  rewrite H0.
  reflexivity.
Qed.

End Rsimpl.