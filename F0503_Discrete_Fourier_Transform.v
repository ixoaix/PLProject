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
Require Import PL.Rcompute PL.Ccompute.
Require Import Coq.Lists.List.

Local Open Scope C_scope.
Delimit Scope C_scope with C.

Notation "[ ]" := nil (format "[ ]") : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope.
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)) : list_scope.
Infix "::" := cons (at level 60, right associativity) : list_scope.
Infix "++" := app (right associativity, at level 60) : list_scope.


(** The function below computes the kth element of Discrete Fourier Transform of a list of complex numbers 
by DEFINITION, not FFT. *)
Fixpoint Fourier (X : list C) (n : R) (k len : nat) : C :=
  match X with
    | nil => (0%R , 0%R)
    | (x :: X')%list => x * (exp_complex (-2 * PI * n * (INR k) * / (INR len))) + (Fourier X' (n + 1) k len)
  end.


(**  Now define the algorithm of FFT. First define some useful functions.*)
(** Selecting the elements of even/odd indices out of a list. Used in FFT.*)
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

(** Pointwise operation on two complex lists. Used in FFT.*)
Fixpoint ListOp (l1: list C) (l2: list C) (Op: C->C->C) (default: list C): list C :=
  match l1, l2 with
     | nil, nil => nil
     | (x1 :: l1' ), (x2 :: l2') => (Op x1 x2) :: ListOp l1' l2' Op default
     | nil, _ => default
     | _, nil => default 
  end.

(** Generating the phase factor used in FFT.*)
Fixpoint PhaseGen (n:nat) (m: nat): list C :=
  match n with
    | O => [(1%R,0%R)]
    | S n' => PhaseGen n' m ++ [(exp_complex (-(IZR (Z.of_nat n)) * 2 * PI / (IZR (Z.of_nat m))))]
  end.
Definition Phase (N: nat): list C:= PhaseGen N (2*N).

(** Checking the length of list X.*)
Definition lenX_pow_2_n_1 (X : list C) : Prop :=
  exists N, Datatypes.length X = Init.Nat.pow 2 N.
(* equal of nat *)
Definition lenX_pow_2_n_2 (X : list C) : Prop :=
  exists N, Z.of_nat (Datatypes.length X) = Z.pow 2 N.
(* equal of Z *)

(** This function describes the algorithm of FFT. The length of list x must be 2^M. *)
Fixpoint FFT (x:list C) (M:nat): list C :=
  match M with
  | O => x
  | S M' => ListOp (FFT (EvenList x) M') (ListOp (Phase (2^M')) (FFT (OddList x) M') Cmult []) Cplus [] 
                  ++ ListOp (FFT (EvenList x) M') (ListOp (Phase (2^M')) (FFT (OddList x) M') Cmult []) Cminus []
  end.

(**  Below are some useful intermediate results for the proof. These come from the derivation of the algorithm of FFT.*)

(** This is the even term of the Fourier transform *)
Fixpoint Fourier_even (X : list C) (n : R) (k len : nat) : C :=
  match X with
    | nil => (0%R , 0%R)
    | (x :: X')%list => x * (exp_complex (-2 * PI * 2 * n * (INR k) * / (2 * (INR len) ))) + (Fourier_even X' (n + 1) k len)
  end.

(** This is the odd term of the Fourier transform *)
Fixpoint Fourier_odd (X : list C) (n : R) (k len : nat) : C :=
  match X with
    | nil => (0%R , 0%R)
    | (x :: X')%list => x * (exp_complex (-2 * PI * (2 * n + 1) * (INR k) * / (2 * (INR len) ))) + (Fourier_odd X' (n + 1) k len)
  end.

Lemma Fourier_nMinus1: forall (X : list C) (n : R) (k len : nat),
  len <> 0%nat -> Fourier X (n + 1) k len = exp_complex (-2 * PI * (INR k) * / (INR len)) * Fourier X n k len.
Proof.
  intros.
  revert n; induction X.
  {
  intros.
  simpl.
  pose proof exp_mult_0_1 (-2 * PI * INR k * / INR len).
  rewrite H0.
  reflexivity.
  }
  intros.
  specialize (IHX (n + 1)%R).
  simpl.
  pose proof Cmult_plus_distr_l (exp_complex (-2 * PI * INR k * / INR len)) (a * exp_complex (-2 * PI * n * INR k * / INR len)) (Fourier X (n + 1) k len).
  rewrite H0.
  clear H0 H.
  rewrite <- IHX.
  assert (exp_complex (-2 * PI * INR k * / INR len) *
(a * exp_complex (-2 * PI * n * INR k * / INR len)) = a * exp_complex (-2 * PI * (n + 1) * INR k * / INR len)).
  {
  pose proof Cmult_assoc_r (exp_complex (-2 * PI * INR k * / INR len)) a (exp_complex (-2 * PI * n * INR k * / INR len)).
  rewrite <- H.
  pose proof Cmult_comm (exp_complex (-2 * PI * INR k * / INR len)) a.
  rewrite H0.
  assert (exp_complex (-2 * PI * INR k * / INR len) *
exp_complex (-2 * PI * n * INR k * / INR len) = exp_complex (-2 * PI * (n + 1) * INR k * / INR len)).
  {
  clear.
  pose proof exp_mult (-2 * PI * INR k * / INR len) (-2 * PI * n * INR k * / INR len).
  pose proof UseByFourier_nMinus1_1 (-2 * PI)%R (INR k * / INR len) n.
  rewrite H.
  pose proof Rmult_assoc (-2 * PI)%R (INR k) (/ INR len).
  rewrite <- H1 in H0.
  pose proof Rmult_assoc (-2 * PI * n) (INR k) (/ INR len).
  rewrite <- H2 in H0.
  rewrite H0.
  pose proof Rmult_assoc (-2 * PI * (n + 1)) (INR k) (/ INR len).
  rewrite <- H3.
  reflexivity.
  }
  pose proof Cmult_assoc_r a (exp_complex (-2 * PI * INR k * / INR len)) (exp_complex (-2 * PI * n * INR k * / INR len)).
  rewrite H1 in H2.
  exact H2.
  }
  rewrite H.
  reflexivity.
Qed.

Lemma Fourier_even_nMinus1: forall (X : list C) (n : R) (k len : nat),
  len <> 0%nat -> Fourier_even X (n + 1) k len = exp_complex (-2 * PI * (INR k) * / (INR len)) * Fourier_even X n k len.
Proof.
  intros.
  revert n; induction X.
  {
  intros.
  simpl.
  pose proof exp_mult_0_1 (-2 * PI * INR k * / INR len).
  rewrite H0.
  reflexivity.
  }
  intros.
  specialize (IHX (n + 1)%R).
  simpl.
  pose proof Cmult_plus_distr_l (exp_complex (-2 * PI * INR k * / INR len)) (a * exp_complex (-2 * PI * 2 * n * INR k * / (2 * INR len))) (Fourier_even X (n + 1) k len).
  rewrite H0.
  clear H0.
  rewrite <- IHX.
  assert (exp_complex (-2 * PI * INR k * / INR len) *
(a * exp_complex (-2 * PI * 2 * n * INR k * / (2 * INR len))) = a * exp_complex (-2 * PI * 2 * (n + 1) * INR k * / (2 * INR len))).
  {
  pose proof Cmult_assoc_r (exp_complex (-2 * PI * INR k * / INR len)) a (exp_complex (-2 * PI * 2 * n * INR k * / (2 * INR len))).
  rewrite <- H0.
  pose proof Cmult_comm (exp_complex (-2 * PI * INR k * / INR len)) a.
  rewrite H1.
  assert (exp_complex (-2 * PI * INR k * / INR len) *
exp_complex (-2 * PI * 2 * n * INR k * / (2 * INR len)) = exp_complex (-2 * PI * 2 * (n + 1) * INR k * / (2 * INR len))).
  {
  pose proof not_0_INR.
  specialize (H2 len H).
  pose proof UseByFourier_even_nMinus1_1 (-2 * PI)%R (INR k) (INR len).
  specialize (H3 H2).
  rewrite H3.
  clear.
  pose proof exp_mult (-2 * PI * 2 * INR k * / (2 * INR len)) (-2 * PI * 2 * n * INR k * / (2 * INR len)).
  pose proof UseByFourier_nMinus1_1 (-2 * PI * 2)%R (INR k * / (2 * INR len)) n.
  rewrite H.
  pose proof Rmult_assoc (-2 * PI * 2)%R (INR k) (/ (2 * INR len)).
  rewrite <- H1 in H0.
  pose proof Rmult_assoc (-2 * PI * 2 * n) (INR k) (/ (2 * INR len)).
  rewrite <- H2 in H0.
  rewrite H0.
  pose proof Rmult_assoc (-2 * PI * 2 * (n + 1)) (INR k) (/ (2 * INR len)).
  rewrite <- H3.
  reflexivity.
  }
  pose proof Cmult_assoc_r a (exp_complex (-2 * PI * INR k * / INR len)) (exp_complex (-2 * PI * 2 * n * INR k * / (2 * INR len))).
  rewrite H2 in H3.
  exact H3.
  }
  rewrite H0.
  reflexivity.
Qed.

Lemma Fourier_odd_nMinus1: forall (X : list C) (n : R) (k len : nat),
  len <> 0%nat -> Fourier_odd X (n + 1) k len = exp_complex (-2 * PI * (INR k) * / (INR len)) * Fourier_odd X n k len.
Proof.
  intros.
  revert n; induction X.
  {
  intros.
  simpl.
  pose proof exp_mult_0_1 (-2 * PI * INR k * / INR len).
  rewrite H0.
  reflexivity.
  }
  intros.
  specialize (IHX (n + 1)%R).
  simpl.
  pose proof Cmult_plus_distr_l (exp_complex (-2 * PI * INR k * / INR len)) (a * exp_complex (-2 * PI * (2 * n + 1) * INR k * / (2 * INR len))) (Fourier_odd X (n + 1) k len).
  rewrite H0.
  clear H0.
  rewrite <- IHX.
  assert (exp_complex (-2 * PI * INR k * / INR len) *
(a * exp_complex (-2 * PI * (2 * n + 1) * INR k * / (2 * INR len))) = a * exp_complex (-2 * PI * (2 * (n + 1) + 1) * INR k * / (2 * INR len))).
  {
  pose proof Cmult_assoc_r (exp_complex (-2 * PI * INR k * / INR len)) a (exp_complex (-2 * PI * (2 * n + 1) * INR k * / (2 * INR len))).
  rewrite <- H0.
  pose proof Cmult_comm (exp_complex (-2 * PI * INR k * / INR len)) a.
  rewrite H1.
  assert (exp_complex (-2 * PI * INR k * / INR len) *
exp_complex (-2 * PI * (2 * n + 1) * INR k * / (2 * INR len)) = exp_complex (-2 * PI * (2 * (n + 1) + 1) * INR k * / (2 * INR len))).
  {
  pose proof not_0_INR.
  specialize (H2 len H).
  pose proof UseByFourier_odd_nMinus1_1 (-2 * PI)%R (INR k) n (INR len).
  specialize (H3 H2).
  pose proof exp_mult (-2 * PI * INR k * / INR len) (-2 * PI * (2 * n + 1) * INR k * / (2 * INR len)).
  rewrite H4 H3.
  reflexivity.
  }
  clear IHX H0 H1.
  pose proof Cmult_eq_compat_l.
  specialize (H0 a (exp_complex (-2 * PI * INR k * / INR len) *
     exp_complex (-2 * PI * (2 * n + 1) * INR k * / (2 * INR len))) (exp_complex (-2 * PI * (2 * (n + 1) + 1) * INR k * / (2 * INR len))) H2).
  pose proof Cmult_assoc_r a (exp_complex (-2 * PI * INR k * / INR len)) (exp_complex (-2 * PI * (2 * n + 1) * INR k * / (2 * INR len))).
  rewrite <- H1 in H0.
  rewrite H0.
  reflexivity.
  }
  rewrite H0.
  reflexivity.
Qed.

(* Fourier_split2_1 *)
Lemma Fourier_split2_1: forall (X : list C) (k len : nat),
  len <> 0%nat -> Fourier_even X 0 k len = Fourier X 0 k len.
Proof.
  intros.
  induction X.
  {
  simpl.
  reflexivity.
  }
  simpl.
  pose proof compute_1 (-2 * PI * 2) (INR k) (2 * (INR len)).
  rewrite H0.
  pose proof compute_1 (-2 * PI) (INR k) (INR len).
  rewrite H1.
  clear H0 H1.
  pose proof Rplus_0_l 1.
  rewrite H0.
  pose proof Fourier_even_nMinus1 X 0 k len.
  specialize (H1 H).
  rewrite H0 in H1.
  rewrite H1.
  pose proof Fourier_nMinus1 X 0 k len.
  specialize (H2 H).
  rewrite H0 in H2.
  rewrite H2.
  rewrite IHX.
  reflexivity.
Qed.

(* Fourier_split2_2 *)
Lemma Fourier_split2_2: forall (X : list C) (k len : nat),
  len <> 0%nat -> Fourier_odd X 0 k len = (exp_complex (-2 * PI * (INR k ) * / (2 * INR len) )) * Fourier X 0 k len.
Proof.
  intros.
  induction X.
  {
  simpl.
  pose proof exp_mult_0_1 (-2 * PI * (INR k) * / (2 * INR len)).
  rewrite H0.
  reflexivity.
  }
  simpl.
  pose proof compute_1 (-2 * PI) (INR k) (INR len).
  rewrite H0.
  pose proof Rmult_0_r 2.
  rewrite H1.
  pose proof Rplus_0_l 1.
  rewrite H2.
  pose proof Rmult_1_r (-2 * PI).
  rewrite H3.
  clear H0 H1 H2 H3.
  pose proof Fourier_odd_nMinus1 X 0 k len.
  specialize (H0 H).
  rewrite IHX in H0.
  pose proof Rplus_0_l 1.
  rewrite H1 in H0.
  rewrite H0.
  pose proof Fourier_nMinus1 X 0 k len.
  specialize (H2 H).
  rewrite H1 in H2.
  rewrite H2.
  pose proof exp_0_mult_r a.
  rewrite H3.
  clear.
  pose proof Cmult_plus_distr_l (exp_complex (-2 * PI * (INR k) * / (2 * (INR len)))) a (exp_complex (-2 * PI * (INR k) * / (INR len)) * Fourier X 0 k len).
  rewrite H; clear.
  pose proof Cmult_comm a (exp_complex (-2 * PI * (INR k) * / (2 * (INR len)))).
  rewrite H; clear.
  pose proof Cmult_assoc_r (exp_complex (-2 * PI * (INR k) * / (2 * (INR len)))) (exp_complex (-2 * PI * (INR k) * / (INR len))) (Fourier X 0 k len).
  rewrite <- H; clear.
  pose proof Cmult_assoc_r (exp_complex (-2 * PI * (INR k) * / (INR len))) (exp_complex (-2 * PI * (INR k) * / (2 * (INR len)))) (Fourier X 0 k len).
  rewrite <- H; clear.
  pose proof Cmult_comm (exp_complex (-2 * PI * (INR k) * / (INR len))) (exp_complex (-2 * PI * (INR k) * / (2 * (INR len)))).
  rewrite H; clear.
  reflexivity.
Qed.

(** Split Fourier transform into odd and even when k < N / 2*)
Lemma Fourier_split1: forall (X : list C) (k len : nat),
  len <> 0%nat -> Fourier X 0 k (2 * len) = Fourier_even (EvenList X) 0 k len + Fourier_odd (OddList X) 0 k len.
Proof.
  intros.
  induction X.
  {
  simpl.
  unfold Cplus.
  simpl.
  pose proof Rplus_0_l 0.
  rewrite H0.
  reflexivity.
  }
  {
  simpl.
  pose proof compute_1 (-2 * PI)%R (INR k) (INR (2 * len)).
  pose proof compute_1 (-2 * PI * 2)%R (INR k) (2 * (INR len)).
  rewrite H0 H1.
  clear H0 H1.
  pose proof Rplus_0_l 1.
  rewrite H0; clear H0.
  pose proof Fourier_nMinus1 X 0 k (2 * len).
  assert (2 <> 0)%nat.
  congruence.
  pose proof Nat.neq_mul_0 2 len.
  destruct H2; clear H3.
  assert (2 <> 0 /\ len <> 0).
  split; [exact H1 | exact H].
  specialize (H2 H3).
  specialize (H0 H2).
  clear H1 H2 H3.
  pose proof Rplus_0_l 1.
  rewrite H1 in H0; clear H1.
  assert (Fourier X 1 k (2 * len) = Fourier_even (OddList X) 1 k len + Fourier_odd (EvenList X) 0 k len).
  2: {
  rewrite H1.
  pose proof Cplus_assoc_r (a * exp_complex 0) (Fourier_even (OddList X) 1 k len) (Fourier_odd (EvenList X) 0 k len).
  rewrite H2.
  reflexivity.
  }
  rewrite H0; clear H0.
  pose proof Fourier_even_nMinus1 (OddList X) 0 k len.
  specialize (H0 H).
  pose proof Fourier_split2_1 (OddList X) k len.
  specialize (H1 H).
  rewrite H1 in H0; clear H1.
  pose proof Fourier_split2_2 (EvenList X) k len.
  specialize (H1 H).
  pose proof Fourier_split2_1 (EvenList X) k len.
  specialize (H2 H).
  rewrite H2 in IHX; clear H2.
  pose proof Fourier_split2_2 (OddList X) k len.
  specialize (H2 H).
  rewrite H2 in IHX; clear H2.
  pose proof Rplus_0_l 1.
  rewrite H2 in H0.
  clear H2.
  rewrite IHX; clear IHX.
  pose proof Cmult_plus_distr_l (exp_complex (-2 * PI * (INR k) * / (INR (2 * len)))) (Fourier (EvenList X) 0 k len) (exp_complex (-2 * PI * (INR k) * / (2 * (INR len))) * Fourier (OddList X) 0 k len).
  rewrite H2; clear H2.
  assert (2 * INR len = INR (2 * len))%R.
  {
  clear.
  pose proof mult_INR 2 len.
  rewrite H.
  assert (2 = INR 2)%R.
  constructor.
  rewrite H0.
  reflexivity.
  }
  rewrite H2 in H1.
  rewrite <- H1; clear H1.
  pose proof Cmult_assoc_r (exp_complex (-2 * PI * (INR k) * / (INR (2 * len)))) (exp_complex (-2 * PI * (INR k) * / (INR (2 * len)))) (Fourier (OddList X) 0 k len).
  rewrite H2.
  rewrite <- H1; clear H1.
  assert (exp_complex (-2 * PI * (INR k) * / (INR (2 * len))) * exp_complex (-2 * PI * (INR k) * / (INR (2 * len))) = exp_complex (-2 * PI * (INR k) * / (INR len))).
  {
  pose proof exp_mult (-2 * PI * (INR k) * / (INR (2 * len))) (-2 * PI * (INR k) * / (INR (2 * len))).
  pose proof UseByFourier_split1_1 (-2 * PI * (INR k)) (INR len).
  pose proof not_INR len 0.
  simpl in H4.
  specialize (H4 H).
  specialize (H3 H4).
  rewrite H2 in H3.
  rewrite H3 in H1.
  apply H1.
  }
  rewrite H1.
  rewrite <- H0.
  apply Cplus_comm.
  }
Qed.

(** Split Fourier transform into odd and even when k > N / 2*)
Lemma Fourier_split3_1: forall (X : list C) (k len : nat),
  len <> 0 -> Fourier_even X 0 k len = Fourier X 0 (k - len) len.
Proof.
Admitted.

Lemma Fourier_split3_2: forall (X : list C) (k len : nat),
  len <> 0 -> X = nil \/ Fourier_odd X 0 k len = (exp_complex (-2 * PI * (INR k) * / (INR (2 * len)) )) * Fourier X 0 k len.
Proof.
Admitted.

Lemma FstHalf: forall (X: list C) (k: nat) (len: nat),
k <= len - 1 ->
Fourier X 0 k (2 * len) = Fourier (EvenList X) 0 k len + (exp_complex (-2 * PI * (INR k) * / (2 * INR len) )) * Fourier (OddList X) 0 k len.
Proof.
Admitted.

Lemma SndHalf: forall (X: list C) (k: nat) (len: nat),
len - 1 < k->
Fourier X 0 k (2 * len) = Fourier (EvenList X) 0 (k - len) len - (exp_complex (-2 * PI * (INR (k - len)) * / (2 * INR len) )) * Fourier (OddList X) 0 (k - len) len.
Proof.
Admitted.


Lemma FFTSplit: forall (x:list C)(M: nat)(a: list C)(b: list C),
(forall (k: nat), (k <= 2^(M - 1) - 1) -> Fourier x 0 k (length x) = nth k a (0%R, 0%R)/\ Fourier x 0 (k + 2^(M-1)) (length x) = nth k b (0%R, 0%R)) ->
forall (k: nat), (k <= 2^M - 1) -> Fourier x 0 k (length x) = nth k (a++b) (0%R, 0%R).
Proof.
Admitted.

Lemma nthListOp: forall (l1: list C) (l2: list C) (Op: C->C->C) (default: list C) (k: nat) (default0: C),
nth k (ListOp l1 l2 Op default) default0 = Op (nth k l1 default0) (nth k l2 default0).
Proof.
Admitted.

Lemma EvenLength: forall (x: list C) (M: nat),
length x = 2 ^ S M -> length (EvenList x) = (2 ^ M) .
Proof.
Admitted.

Lemma OddLength: forall (x: list C) (M: nat),
length x = 2 ^ S M -> length (OddList x) = (2 ^ M) .
Proof.
Admitted.

Lemma Phase_k: forall(k : nat) (M: nat),
nth k (Phase (2 ^ M)) (0%R, 0%R) = exp_complex (-2 * PI * INR k * / (2 * INR (2 ^ M))).
Proof.
Admitted.

Lemma ineq: forall(k0: nat) (M: nat),
2^(S M - 1) - 1 < (k0 + 2 ^ (S M - 1)).
Proof.
Admitted.

(**  This is our ultimate goal.*)
Definition FFTCorrect : forall (M:nat) (x:list C) (k:nat),
  (length x = Nat.pow 2 M /\ k <= Nat.pow 2 M - 1) -> 
  Fourier x 0 k (length x) = nth k (FFT x M) (0%R, 0%R).
Proof.
  induction M.
  + intros. simpl. simpl in H.
    destruct H. rewrite H. destruct x.
    ++ unfold Fourier. destruct k; simpl; reflexivity.
    ++ destruct x. 
          2:{simpl in H. discriminate H. }
          simpl.
          pose proof compute_1 (-2*PI) (INR k) 1%R .
          rewrite H1. rewrite expcomplex_0. 
          destruct k. destruct c. unfold Cmult, Cplus. simpl. repeat rewrite Rmult_0_r. 
          repeat rewrite Rmult_1_r. repeat rewrite Rplus_0_r. repeat rewrite Rminus_0_r.
          repeat rewrite Rplus_0_l. reflexivity. 
          simpl in H0. apply le_n_0_eq in H0. discriminate H0.
  + intros. destruct H. simpl. revert H0. apply FFTSplit. split. 
    ++ repeat rewrite nthListOp.
          pose proof FstHalf x k0 (2^(S M - 1)) H0.
          rewrite H. simpl; rewrite Nat.add_0_r. 
          simpl in H1; rewrite Nat.sub_0_r in H1; rewrite Nat.add_0_r in H1. 
          pose proof IHM (EvenList x) k0. pose proof IHM (OddList x) k0.
          pose proof EvenLength _ _ H. pose proof OddLength _ _ H.
          simpl in H0; rewrite Nat.sub_0_r in H0. 
          assert(Fourier (EvenList x) 0 k0 (length (EvenList x)) = nth k0 (FFT (EvenList x) M) (0%R, 0%R)).
          apply H2. split. exact H4. exact H0.
          assert(Fourier (OddList x) 0 k0 (length (OddList x)) = nth k0 (FFT (OddList x) M) (0%R, 0%R)).
          apply H3. split. exact H5. exact H0.
          pose proof Phase_k k0 M. 
          rewrite H5 in H7; rewrite H4 in H6; rewrite H6 H7 in H1; rewrite H8; rewrite H1. 
          reflexivity.
    ++ repeat rewrite nthListOp. 
          pose proof ineq k0 M.
          pose proof SndHalf x (k0 + 2 ^ (S M - 1)) (2^(S M - 1)) .
          rewrite H. simpl in H1; rewrite Nat.sub_0_r in H1; rewrite plus_comm in H1.
          simpl in H2; rewrite Nat.sub_0_r in H2; rewrite Nat.add_0_r in H2.
          rewrite plus_comm in H2. rewrite minus_plus in H2.
          pose proof IHM (EvenList x) k0. pose proof IHM (OddList x) k0.
          pose proof EvenLength _ _ H. pose proof OddLength _ _ H.
          simpl in H0; rewrite Nat.sub_0_r in H0. 
          assert(Fourier (EvenList x) 0 k0 (length (EvenList x)) = nth k0 (FFT (EvenList x) M) (0%R, 0%R)).
          apply H3. split. exact H5. exact H0.
          assert(Fourier (OddList x) 0 k0 (length (OddList x)) = nth k0 (FFT (OddList x) M) (0%R, 0%R)).
          apply H4. split. exact H6. exact H0.
          pose proof Phase_k k0 M.
          pose proof H2 H1.
          rewrite H5 in H7; rewrite H6 in H8; rewrite H7 H8 in H10; rewrite H9.
          simpl; rewrite Nat.add_0_r; rewrite Nat.sub_0_r; rewrite plus_comm.
          rewrite H10.
          reflexivity. 
Qed.
