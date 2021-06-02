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

Lemma UseByCmult_assoc_r_1:forall (x y z a b c : R),
  (x * y - a * b ) * z -
  (x * b + a * y ) * c = x * (y * z - b * c) -
  a * (y * c + b * z).
Proof.
  intros.
  pose proof Rmult_minus_distr_r z (x * y) (a * b).
  pose proof Rmult_minus_distr_l x (y * z) (b * c).
  rewrite H H0.
  pose proof Rmult_plus_distr_r (x * b) (a * y) c.
  pose proof Rmult_plus_distr_l a (y * c) (b * z).
  rewrite H1 H2.
  pose proof Rmult_assoc x y z.
  pose proof Rmult_assoc x b c.
  pose proof Rmult_assoc a y c.
  pose proof Rmult_assoc a b z.
  rewrite <- H3.
  rewrite <- H4.
  rewrite <- H5.
  rewrite <- H6.
  unfold Rminus.
  pose proof Ropp_plus_distr (x * b * c) (a * y * c).
  pose proof Ropp_plus_distr (a * y * c) (a * b * z).
  rewrite H7 H8.
  clear.
  pose proof Rplus_assoc (x * y * z + - (a * b * z)) (- (x * b * c)) (- (a * y * c)).
  rewrite <- H.
  pose proof Rplus_assoc (x * y * z + - (x * b * c)) (- (a * y * c)) (- (a * b * z)).
  rewrite <- H0.
  assert (forall a b c d : R, a + b + c + d = a + c + d + b).
  {
  clear. intros.
  pose proof Rplus_assoc a b (c + d).
  pose proof Rplus_assoc (a + b) c d.
  rewrite <- H0 in H. clear H0.
  pose proof Rplus_comm b (c + d).
  rewrite H0 in H. clear H0.
  pose proof Rplus_assoc a (c + d) b.
  rewrite <- H0 in H. clear H0.
  pose proof Rplus_assoc a c d.
  rewrite <- H0 in H. clear H0.
  exact H.
  }
  apply H1.
Qed.

Lemma Rplus_assoc_4:forall a b c d : R,
  a + b + (c + d) = a + c + (d + b).
Proof.
  intros.
  pose proof Rplus_assoc a b (c + d).
  pose proof Rplus_comm b (c + d).
  rewrite H0 in H. clear H0.
  pose proof Rplus_assoc a (c + d) b.
  rewrite <- H0 in H. clear H0.
  pose proof Rplus_assoc a c d.
  rewrite <- H0 in H. clear H0.
  pose proof Rplus_assoc (a + c) d b.
  rewrite H0 in H. clear H0.
  exact H.
Qed.

Lemma UseByCmult_assoc_r_2:forall (x y z a b c : R),
(x * y - a * b) * c + (x * b + a * y) * z = x * (y * c + b * z) +
 a * (y * z - b * c).
Proof.
  intros.
  pose proof Rmult_minus_distr_r c (x * y) (a * b).
  pose proof Rmult_plus_distr_l x (y * c) (b * z).
  rewrite H H0.
  pose proof Rmult_plus_distr_r (x * b) (a * y) z.
  pose proof Rmult_minus_distr_l a (y * z) (b * c).
  rewrite H1 H2.
  pose proof Rmult_assoc x y c.
  pose proof Rmult_assoc x b z.
  pose proof Rmult_assoc a y z.
  pose proof Rmult_assoc a b c.
  rewrite <- H3.
  rewrite <- H4.
  rewrite <- H5.
  rewrite <- H6.
  unfold Rminus.
  clear.
  apply Rplus_assoc_4.
Qed.

Lemma UseByCmult_plus_distr_l_1:forall (x y z a b c : R),
  x * (y + z) - a * (b + c) = x * y - a * b + (x * z - a * c).
Proof.
  intros.
  pose proof Rmult_plus_distr_l x y z.
  pose proof Rmult_plus_distr_l a b c.
  rewrite H H0.
  unfold Rminus.
  pose proof Ropp_plus_distr (a * b) (a * c).
  rewrite H1.
  pose proof Rplus_assoc_4 (x*y) (x*z) (-(a*b)) (-(a*c)).
  pose proof Rplus_comm (-(a*c)) (x*z).
  rewrite H3 in H2.
  exact H2.
Qed.

Lemma UseByCmult_plus_distr_l_2:forall (x y z a b c : R),
  x * (b + c) + a * (y + z) = x * b + a * y + (x * c + a * z).
Proof.
  intros.
  pose proof Rmult_plus_distr_l x b c.
  pose proof Rmult_plus_distr_l a y z.
  rewrite H H0.
  pose proof Rplus_assoc_4 (x*b) (x*c) (a*y) (a*z).
  pose proof Rplus_comm (a*z) (x*c).
  rewrite H2 in H1.
  exact H1.
Qed.

Lemma UseByCmult_plus_distr_r_1:forall (x y z a b c : R),
  (x + y) * z - (a + b) * c = x * z - a * c + (y * z - b * c).
Proof.
  intros.
  pose proof Rmult_plus_distr_r x y z.
  pose proof Rmult_plus_distr_r a b c.
  rewrite H H0.
  unfold Rminus.
  pose proof Ropp_plus_distr (a * c) (b * c).
  rewrite H1.
  pose proof Rplus_assoc_4 (x*z) (y*z) (-(a*c)) (-(b*c)).
  pose proof Rplus_comm (-(b*c)) (y*z).
  rewrite H3 in H2.
  exact H2.
Qed.

Lemma UseByCmult_plus_distr_r_2:forall (x y z a b c : R),
  (x + y) * c + (a + b) * z = x * c + a * z + (y * c + b * z).
Proof.
  intros.
  pose proof Rmult_plus_distr_r x y c.
  pose proof Rmult_plus_distr_r a b z.
  rewrite H H0.
  pose proof Rplus_assoc_4 (x*c) (y*c) (a*z) (b*z).
  pose proof Rplus_comm (b*z) (y*c).
  rewrite H2 in H1.
  exact H1.
Qed.

Lemma UseByFourier_neq1_1:forall (p q n : R),
  p * q + p * n * q = p * (n + 1) * q.
Proof.
  intros.
  pose proof Rmult_comm p n.
  pose proof Rmult_comm p (n + 1).
  rewrite H H0. clear.
  pose proof Rmult_1_l (p * q).
  rewrite <- H.
  pose proof Rmult_plus_distr_r 1 n (p * q).
  pose proof Rmult_assoc n p q.
  rewrite H1.
  rewrite <- H0.
  pose proof Rplus_comm 1 n.
  rewrite H2.
  pose proof Rmult_assoc (n + 1) p q.
  rewrite H3.
  reflexivity.
Qed.

Lemma UseByFourier_even_neq1_1:forall (p q r : R),
  r <> 0 -> p * q * / r = p * 2 * q * / (2 * r).
Proof.
  intros.
  pose proof Rinv_mult_distr 2 r.
  pose proof not_0_IZR 2.
  assert ( 2%Z <> 0%Z ).
  congruence.
  pose proof H1 H2.
  pose proof H0 H3.
  pose proof H4 H.
  rewrite H5.
  pose proof Rmult_assoc (p * 2 * q) (/2) (/r).
  rewrite <- H6.
  pose proof Rmult_assoc p 2 q.
  pose proof Rmult_comm 2 q.
  rewrite H8 in H7.
  pose proof Rmult_assoc p q 2.
  rewrite <- H9 in H7.
  rewrite H7.
  pose proof Rmult_assoc (p * q) 2 (/2).
  pose proof Rinv_l 2.
  specialize (H11 H3).
  pose proof Rmult_comm 2 (/2).
  rewrite <- H12 in H11.
  rewrite H11 in H10.
  rewrite H10.
  pose proof Rmult_1_r (p * q).
  rewrite H13.
  reflexivity.
Qed.

End Rsimpl.