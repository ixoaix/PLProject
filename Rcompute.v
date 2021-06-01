Require Import Reals ssreflect.

Module Rsimpl.

Local Open Scope R.

Lemma compute_1: forall (p k l : R),
  p * 0 * k * / l = 0.
Proof.
  intros.
  pose proof Rmult_0_r (p).
  rewrite H.
  pose proof Rmult_0_l (k * / l).
  pose proof Rmult_assoc 0 k (/l).
  rewrite <- H1 in H0.
  rewrite H0.
  reflexivity.
Qed.

End Rsimpl.