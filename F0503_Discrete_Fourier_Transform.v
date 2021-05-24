(** Discrete Fourier transformation can be used to compute big number's
    multiplication. FFT is a well-known efficient algorithm to calculate
    discrete fourier transformation. Your should learn how this algorithm works
    and prove its correctness in Coq. You need to either define this algorithm
    using complex numbers (you may find some library in Coq's standard library
    or other Coq's user's contribution) or via an abstract ring with some extra
    properties.

    You only need to define this algorithm as a Coq function or a Coq relation
    (small step description of this algorithm). You do not need to implement it
    in a programming language like C. You do not need to verify its 
    implementation in any programming language. *)

(* 2021-05-07 20:39 *)
From Coq Require Import Reals ssreflect.
Require Import PL.Imp.

Definition C := (R * R)%type.

(** *** Arithmetic operations *)

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

Notation "[ ]" := nil (format "[ ]") : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope.
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)) : list_scope.
Infix "::" := cons (at level 60, right associativity) : list_scope.
Infix "++" := app (right associativity, at level 60) : list_scope.

Fixpoint EvenList (l:list C) : list C := 
  match l with
     | nil => nil
     | (x :: l' )%list=> x :: OddList l'
end
with OddList (l:list C) : list C := 
  match l with
     | nil => nil
     | (_ :: l' )%list=> EvenList l'
    end.

Definition exp_complex (x : R) : C :=
  (cos x, sin x).

Definition lenX_pow_2_n_1 (X : list C) : Prop :=
  exists N, Z.of_nat (Datatypes.length X) = Zpower.two_power_nat N.
(* equal of Z *)

Definition lenX_pow_2_n_2 (X : list C) : Prop :=
  exists N, Datatypes.length X = Init.Nat.pow 2 N.
(* equal of nat *)

Definition lenX_pow_2_n_3 (X : list C) : Prop :=
  exists N, Z.of_nat (Datatypes.length X) = Z.pow 2 N.
(* equal of Z *)

Fixpoint Fourier_sum (X : list C) (n : R) (k : Z) : C :=
  match X with
    | nil => (0%R , 0%R)
    | (x :: X')%list => x * (exp_complex (-2 * PI * n * (IZR k) / (INR (Datatypes.length X)))) + (Fourier_sum X' (n + 1) k)
  end.

Definition Fourier (X : list C) (k : Z) : C :=
  Fourier_sum X 0%R k.
(* Function 'Fourier' means the k_th term of Fourier transform of list X. *)

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

Lemma example1: forall (x y z w : C) , EvenList [x; y; z; w] = [x; z]%list.
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Lemma example2: forall (x y z : C) , OddList [x; y; z] = [y]%list.
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Lemma example3: forall (x y z w : C) , lenX_pow_2_n_1 [x; y; z; w].
Proof.
  intros.
  unfold lenX_pow_2_n_1.
  exists 2%nat.
  unfold Zpower.two_power_nat.
  simpl.
  reflexivity.
Qed.

Lemma example4: forall (x y z w : C) , lenX_pow_2_n_2 [x; y; z; w].
Proof.
  intros.
  unfold lenX_pow_2_n_2.
  exists 2%nat.
  simpl.
  lia.
Qed.

Lemma example5: forall (x y z w : C) , lenX_pow_2_n_3 [x; y; z; w].
Proof.
  intros.
  unfold lenX_pow_2_n_3.
  exists 2.
  simpl.
  lia.
Qed.
