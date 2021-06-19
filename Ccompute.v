Require Import Reals ssreflect.
Require Import PL.Rcompute.

(** Definition of complex numbers based on real numbers defined in coq's standard library.*)
Definition C := (R * R)%type.

(** Arithmetic operations *)
Definition Cplus (x y : C) : C := (Rplus (fst x) (fst y), Rplus (snd x) (snd y)).
Definition Copp (x : C) : C := (Ropp(fst x), Ropp(snd x)).
Definition Cminus (x y : C) : C := Cplus x (Copp y).
Definition Cmult (x y : C) : C := (Rminus (Rmult (fst x) (fst y))  (Rmult (snd x) (snd y)), Rplus (Rmult(fst x) (snd y)) (Rmult(snd x) (fst y))).
Definition Cinv (x : C) : C := (Rdiv (fst x) (Rplus (fst x ^ 2) (snd x ^ 2)), Ropp (Rdiv (snd x) (fst x ^ 2 + snd x ^ 2))).
Definition Cdiv (x y : C) : C := Cmult x (Cinv y).

Declare Scope C_scope.

Local Open Scope C_scope.
Delimit Scope C_scope with C.
Infix "+" := Cplus : C_scope.
Notation "- x" := (Copp x) : C_scope.
Infix "-" := Cminus : C_scope.
Infix "*" := Cmult : C_scope.
Notation "/ x" := (Cinv x) : C_scope.
Infix "/" := Cdiv : C_scope.

Notation "(x, y)" := C : C_scope.

(** A convenient expression of  e^ix based on Euler's formula.*)
Definition exp_complex (x : R) : C :=
  (cos x, sin x).

Lemma exp_mult: forall (x y : R),
  exp_complex x * exp_complex y = exp_complex ( x + y ) .
Proof.
  intros.
  unfold exp_complex.
  unfold Cmult.
  simpl.
  pose proof cos_plus x y.
  rewrite <- H.
  assert ((sin x * cos y + cos x * sin y )%R = (cos x * sin y + sin x * cos y )%R).
  { apply Rplus_comm. }
  rewrite <- H0.
  pose proof sin_plus x y.
  rewrite <- H1.
  reflexivity.
Qed.

Lemma expcomplex_0:
  exp_complex 0 = (1%R , 0%R).
Proof.
  unfold exp_complex.
  pose proof cos_0.
  rewrite H.
  pose proof sin_0.
  rewrite H0.
  reflexivity.
Qed.

Lemma exp_mult_0_1: forall (x : R),
  exp_complex x * (0%R, 0%R) = (0%R, 0%R).
Proof.
  intros.
  unfold exp_complex, Cmult.
  simpl.
  pose proof Rmult_0_r (cos x).
  pose proof Rmult_0_r (sin x).
  rewrite H H0.
  pose proof Rminus_0_r 0.
  pose proof Rplus_0_l 0.
  rewrite H1 H2.
  reflexivity.
Qed.

Lemma exp_mult_0_2: forall (x : R),
  (0%R, 0%R) * exp_complex x = (0%R, 0%R).
Proof.
  intros.
  unfold exp_complex, Cmult.
  simpl.
  pose proof Rmult_0_l (cos x).
  pose proof Rmult_0_l (sin x).
  rewrite H H0.
  pose proof Rminus_0_r 0.
  pose proof Rplus_0_l 0.
  rewrite H1 H2.
  reflexivity.
Qed.

Lemma Cminus_minus (x : C) : --x = x.
Proof.
  destruct x.
  unfold Copp.
  simpl.
  pose proof Ropp_involutive r.
  pose proof Ropp_involutive r0.
  rewrite H H0.
  reflexivity.
Qed.

Lemma Cplus_comm (x y : C) : x + y = y + x.
Proof.
  unfold Cplus.
  pose proof Rplus_comm (fst x)%R (fst y )%R.
  pose proof Rplus_comm (snd x)%R (snd y )%R.
  rewrite H H0.
  reflexivity.
Qed.

Lemma Cplus_assoc_l (x y z : C) : x + y + z = (x + y ) + z.
Proof.
  unfold Cplus.
  simpl.
  reflexivity.
Qed.

Lemma Cplus_assoc_r (x y z : C) : x + y + z = x + (y + z).
Proof.
  unfold Cplus.
  simpl.
  pose proof Rplus_assoc (fst x)%R (fst y )%R (fst z)%R.
  pose proof Rplus_assoc (snd x)%R (snd y )%R (snd z)%R.
  rewrite H H0.
  reflexivity.
Qed.

Lemma Cplus_0_r (x : C) : x + (0%R , 0%R) = x.
Proof.
  unfold Cplus.
  simpl.
  pose proof Rplus_0_r (fst x)%R.
  pose proof Rplus_0_r (snd x)%R.
  rewrite H H0.
  destruct x.
  simpl.
  reflexivity.
Qed.

Lemma Cplus_0_l (x : C) : (0%R , 0%R) + x = x.
Proof.
  unfold Cplus.
  simpl.
  pose proof Rplus_0_l (fst x)%R.
  pose proof Rplus_0_l (snd x)%R.
  rewrite H H0.
  destruct x.
  simpl.
  reflexivity.
Qed.

Lemma Cplus_opp_r (x : C) : x + -x = (0%R , 0%R).
Proof.
  unfold Cplus.
  simpl.
  pose proof Rplus_opp_r (fst x)%R.
  pose proof Rplus_opp_r (snd x)%R.
  rewrite H H0.
  reflexivity.
Qed.

Lemma Copp_plus_distr (z1 z2 : C) : - (z1 + z2) = (- z1 + - z2).
Proof.
  unfold Cplus, Copp.
  simpl.
  pose proof Ropp_plus_distr (fst z1)%R (fst z2)%R.
  pose proof Ropp_plus_distr (snd z1)%R (snd z2)%R.
  rewrite H H0.
  reflexivity.
Qed.

Lemma Copp_minus_distr (z1 z2 : C) : - (z1 - z2) = z2 - z1.
Proof.
  unfold Cminus, Cplus, Copp.
  simpl.
  pose proof Ropp_plus_distr (fst z1)%R (-fst z2)%R.
  pose proof Ropp_plus_distr (snd z1)%R (-snd z2)%R.
  rewrite H H0.
  assert ((- fst z1 + - - fst z2)%R = (fst z2 + - fst z1)%R).
  {
  pose proof Ropp_involutive (fst z2)%R.
  rewrite H1.
  apply Rplus_comm.
  }
  assert ((- snd z1 + - - snd z2)%R = (snd z2 + - snd z1)%R).
  {
  pose proof Ropp_involutive (snd z2)%R.
  rewrite H2.
  apply Rplus_comm.
  }
  rewrite H1 H2.
  reflexivity.
Qed.

Lemma Cmult_comm (x y : C) : x * y = y * x.
Proof.
  unfold Cmult.
  pose proof Rmult_comm (fst x)%R (fst y )%R.
  pose proof Rmult_comm (snd x)%R (snd y )%R.
  pose proof Rmult_comm (fst x)%R (snd y )%R.
  pose proof Rmult_comm (snd x)%R (fst y )%R.
  rewrite H H0 H1 H2.
  pose proof Rplus_comm (snd y * fst x)%R (fst y * snd x)%R.
  rewrite H3.
  reflexivity.
Qed.

Lemma exp_0_mult_l: forall (x : C),
  exp_complex 0 * x = x.
Proof.
  intros.
  unfold exp_complex.
  destruct x.
  pose proof cos_0.
  pose proof sin_0.
  rewrite H H0.
  unfold Cmult.
  simpl.
  pose proof Rmult_1_l r.
  pose proof Rmult_0_l r0.
  pose proof Rmult_1_l r0.
  pose proof Rmult_0_l r.
  rewrite H1 H2 H3 H4.
  pose proof Rminus_0_r r.
  pose proof Rplus_0_r r0.
  rewrite H5 H6.
  reflexivity.
Qed.

Lemma exp_0_mult_r: forall (x : C),
  x * exp_complex 0 = x.
Proof.
  intros.
  pose proof exp_0_mult_l x.
  rewrite <- H at 2.
  apply Cmult_comm.
Qed.

Lemma Cmult_assoc_l (x y z : C) : x * y * z = (x * y ) * z.
Proof.
  reflexivity.
Qed.

Lemma Cmult_assoc_r (x y z : C) : x * y * z = x * (y * z).
Proof.
  unfold Cmult, Copp.
  simpl.
  pose proof UseByCmult_assoc_r_1 (fst x) (fst y ) (fst z) (snd x) (snd y ) (snd z).
  pose proof UseByCmult_assoc_r_2 (fst x) (fst y ) (fst z) (snd x) (snd y ) (snd z).
  rewrite H H0.
  reflexivity.
Qed.

Lemma Cmult_0_r (x : C) : x * (0%R , 0%R) = (0%R , 0%R).
Proof.
  destruct x.
  unfold Cmult.
  simpl.
  pose proof Rmult_0_r r.
  pose proof Rmult_0_r r0.
  rewrite H H0.
  pose proof Rplus_0_r 0.
  pose proof Rminus_0_r 0.
  rewrite H1 H2.
  reflexivity.
Qed.

Lemma Cmult_0_l (x : C) : (0%R , 0%R) * x = (0%R , 0%R).
Proof.
  pose proof Cmult_comm (0%R, 0%R) x.
  pose proof Cmult_0_r x.
  rewrite H H0.
  reflexivity.
Qed.

Lemma Cmult_1_r (x : C) : x * (1%R , 0%R) = x.
Proof.
  destruct x.
  unfold Cmult.
  simpl.
  pose proof Rmult_0_r r.
  pose proof Rmult_0_r r0.
  pose proof Rmult_1_r r.
  pose proof Rmult_1_r r0.
  pose proof Rminus_0_r r.
  pose proof Rplus_0_l r0.
  rewrite H H0 H1 H2 H3 H4.
  reflexivity.
Qed.

Lemma Cmult_1_l (x : C) : (1%R , 0%R) * x = x.
Proof.
  pose proof Cmult_comm (1%R, 0%R) x.
  pose proof Cmult_1_r x.
  rewrite H H0.
  reflexivity.
Qed.


Lemma Cmult_plus_distr_l (x y z : C) : x * (y + z) = x * y + x * z.
Proof.
  unfold Cmult, Cplus.
  simpl.
  pose proof UseByCmult_plus_distr_l_1 (fst x) (fst y ) (fst z) (snd x) (snd y ) (snd z).
  pose proof UseByCmult_plus_distr_l_2 (fst x) (fst y ) (fst z) (snd x) (snd y ) (snd z).
  rewrite H H0.
  reflexivity.
Qed.

Lemma Cmult_plus_distr_r (x y z : C) : (x + y ) * z = x * z + y * z.
Proof.
  unfold Cmult, Cplus.
  simpl.
  pose proof UseByCmult_plus_distr_r_1 (fst x) (fst y ) (fst z) (snd x) (snd y ) (snd z).
  pose proof UseByCmult_plus_distr_r_2 (fst x) (fst y ) (fst z) (snd x) (snd y ) (snd z).
  rewrite H H0.
  reflexivity.
Qed.

Lemma Cmult_eq_compat_l:forall (r r1 r2 : C),
  r1 = r2 -> r * r1 = r * r2.
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.

Lemma Cmult_eq_compat_r:forall (r r1 r2 : C),
  r1 = r2 -> r1 * r = r2 * r.
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.

Lemma Use_By_Fourier_split3_1_2:forall (a b c d : R),
  d <> 0%R -> exp_complex (a * (b - c) * / d) = exp_complex (a * b * / d) * exp_complex (- a * c * / d).
Proof.
  intros.
  pose proof Use_By_Fourier_split3_1_1 a b c d.
  specialize (H0 H).
  rewrite H0.
  pose proof exp_mult (a * b * / d) (- a * c * / d).
  rewrite H1.
  reflexivity.
Qed.

Lemma Cmult_1R: forall (x : C),
  x * (1%R, 0%R) = x.
Proof.
  intros.
  destruct x.
  unfold Cmult.
  simpl.
  pose proof Rmult_1_r r.
  pose proof Rmult_1_r r0.
  pose proof Rmult_0_r r.
  pose proof Rmult_0_r r0.
  pose proof Rplus_0_l r0.
  pose proof Rminus_0_r r.
  rewrite H H0 H1 H2 H3 H4.
  reflexivity.
Qed.

Lemma Cmult_minus1R: forall (x : C),
  x * ((-1)%R, 0%R) = - x.
Proof.
  intros.
  destruct x.
  unfold Cmult.
  simpl.
  assert (r * -1 = -r)%R. ring.
  assert (r0 * -1 = -r0)%R. ring.
  assert (- r - r0 * 0 = -r)%R. ring.
  assert (r * 0 + - r0 = -r0)%R. ring.
  rewrite H H0 H1 H2.
  clear.
  constructor.
Qed.

Lemma Use_by_kMinuslen_1: forall (k len : nat),
  len <> 0 -> len <= k -> exp_complex (-2 * PI * INR (k - len) * / (INR len)) = exp_complex (-2 * PI * INR k * / (INR len)).
Proof.
  intros.
  pose proof minus_INR k len.
  specialize (H1 H0).
  rewrite H1; clear H1.
  pose proof Use_By_Fourier_split3_1_2 (-2 * PI)%R (INR k) (INR len) (INR len).
  pose proof not_INR len 0.
  specialize (H2 H); simpl in H2.
  specialize (H1 H2).
  rewrite H1.
  pose proof Rinv_r_simpl_l (INR len) (- (-2 * PI))%R.
  specialize (H3 H2); clear H2.
  rewrite H3.
  assert (exp_complex (- (-2 * PI)) = (1%R , 0%R)).
  {
  assert (- (-2 * PI) = 2 * PI)%R.
  ring.
  rewrite H2.
  unfold exp_complex.
  pose proof cos_2PI.
  pose proof sin_2PI.
  rewrite H4 H5.
  reflexivity.
  }
  rewrite H2.
  pose proof Cmult_1R (exp_complex (-2 * PI * INR k * / INR len)).
  rewrite H4.
  reflexivity.
Qed.

Lemma Use_by_kMinuslen_2: forall (k len : nat),
  len <> 0 -> len <= k -> exp_complex (-2 * PI * INR (k - len) * / (2 * INR len)) = - exp_complex (-2 * PI * INR k * / (2 * INR len)).
Proof.
  intros.
  pose proof minus_INR k len.
  specialize (H1 H0).
  rewrite H1; clear H1.
  pose proof Use_By_Fourier_split3_1_2 (-2 * PI)%R (INR k) (INR len) (2 * INR len).
  pose proof not_INR len 0.
  specialize (H2 H); simpl in H2.
  pose proof Rmult_integral_contrapositive_currified 2 (INR len).
  assert ( 2%Z <> 0%Z ).
  congruence.
  pose proof not_0_IZR 2.
  specialize (H5 H4).
  specialize (H3 H5 H2).
  specialize (H1 H3).
  rewrite H1.
  assert (- (-2 * PI) * INR len * / (2 * INR len) = PI)%R.
  field.
  exact H2.
  rewrite H6.
  clear.
  unfold exp_complex at 2.
  pose proof cos_PI.
  pose proof sin_PI.
  rewrite H H0; clear.
  apply Cmult_minus1R.
Qed.

Lemma Use_By_SndHalf: forall (a b c : C),
  a - - b * c = a + b * c.
Proof.
  intros.
  unfold Cminus.
  assert (- b * c = - (b * c)).
  {
  destruct b, c.
  unfold Cmult.
  simpl.
  assert (- r * r1 - - r0 * r2 = - (r * r1 - r0 * r2))%R. ring.
  assert (- r * r2 + - r0 * r1 = - (r * r2 + r0 * r1))%R. ring.
  rewrite H H0.
  constructor.
  }
  rewrite H.
  pose proof Cminus_minus (b * c).
  rewrite H0.
  reflexivity.
Qed.