Require Import Reals ssreflect.
Require Import PL.Rcompute.

(** Definition of complex numbers based on real numbers defined in coq's standard library.*)
Definition C := (R * R)%type.

(** Arithmetic operations *)
Definition Cplus (x y : C) : C := (Rplus (fst x) (fst y), Rplus (snd x) (snd y)).
Definition Copp (x : C) : C := (Ropp(fst x), Ropp( -snd x)).
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
