Require Import Reals ssreflect.

Module Rsimpl.

Local Open Scope R.

<<<<<<< Updated upstream
Lemma compute_1: forall (p k l : R),
  p * 0 * k * / l = 0.
=======
Lemma compute_1: forall (k l : R),
  -2 * PI * 0 * k * / l = 0.
>>>>>>> Stashed changes
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