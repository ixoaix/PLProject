From Coq Require Import Reals ssreflect.
Require Import Coq.micromega.Lia.

Lemma ineq2: forall(k0 M: nat),
k0 <= 2 ^ M - 1 -> k0 < 2^M.
Proof.
  intros.
  assert (2 ^ M - 1 < 2 ^ M).
  2: {
  pose proof Nat.le_lt_trans _ _ _ H H0.
  exact H1.
  }
  eapply Nat.sub_lt.
  {
  pose proof Nat.eq_0_gt_0_cases M.
  apply Nat.lt_eq_cases.
  destruct H0.
  {
  right.
  rewrite H0.
  simpl.
  reflexivity.
  }
  pose proof Nat.pow_gt_1 2 M.
  left.
  apply H1.
  auto.
  apply Nat.neq_0_lt_0.
  exact H0.
  }
  auto.
Qed.

Lemma ineq3: forall(k0 M: nat),
 2 ^ M - 1 < k0 ->  2^M <= k0.
Proof.
  intros.
  lia.
Qed.

Lemma ineq4:  forall(k M: nat),
 k <= 2 ^ S M - 1 -> k - 2 ^ M <= 2 ^ M - 1.
Proof.
  intros.
  assert (2 ^ S M - 1 - 2 ^ M = 2 ^ M - 1)%nat.
  {
  simpl.
  lia.
  }
  rewrite <- H0.
  lia.
Qed.

Lemma ineq5: forall (k : nat),
  2 ^ k <> 0.
Proof.
  intros.
  apply Nat.pow_nonzero.
  congruence.
Qed.

Lemma ineq6: forall (k0 M : nat),
  2 ^ M <= 2 ^ M + k0.
Proof.
  intros.
  lia.
Qed.


Lemma ineq: forall(k0: nat) (M: nat),
2^(S M - 1) - 1 < (k0 + 2 ^ (S M - 1)).
Proof.
  intros.
  eapply Nat.lt_le_trans.
  {
  eapply Nat.sub_lt.
  {
  pose proof Nat.eq_0_gt_0_cases M.
  apply Nat.lt_eq_cases.
  destruct H.
  {
  right.
  rewrite H.
  simpl.
  reflexivity.
  }
  pose proof Nat.pow_gt_1 2 (S M - 1).
  left.
  apply H0.
  auto.
  apply Nat.neq_0_lt_0.
  simpl.
  lia.
  }
  auto.
  }
  apply le_plus_r.
Qed.

Lemma eq0: forall M,
(2 * INR (2 ^ M))%R = (INR (2 * 2 ^ M)).
Proof.
  intros.
  pose proof mult_INR 2 (2 ^ M).
  assert (INR 2 = 2)%R.
  constructor.
  rewrite H0 in H.
  rewrite H.
  reflexivity.
Qed.
