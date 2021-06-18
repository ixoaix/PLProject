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
Require Import Coq.micromega.Lia.

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
    | O => []
    | S n' => PhaseGen n' m ++ [(exp_complex (- 2 * PI * (INR n') / (INR m)))]
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

Lemma ListOpLength:forall (l1 l2 : list C)(Op : C->C->C) (default: list C),
length l1 = length l2 -> length (ListOp l1 l2 Op default) = length l1.
Proof.
  induction l1, l2; intros.
  + reflexivity.
  + discriminate H.
  + discriminate H.
  + intros. simpl.
    simpl in H. 
    rewrite <- Nat.compare_eq_iff.
    rewrite Nat.compare_succ.
    rewrite Nat.compare_eq_iff.
    rewrite <- Nat.compare_eq_iff in H.
    rewrite Nat.compare_succ in H.
    simpl in H.
    apply Nat.compare_eq_iff in H.
    apply IHl1. exact H.
Qed.

Lemma EOListLength: forall (n: nat)(x: list C),
length x = (2 * n)%nat  -> length (EvenList x) = n /\ length (OddList x) = n.
Proof.
  induction n.
  + intros; simpl.
    induction x. { simpl; split; reflexivity. } 
    discriminate H.
  + intros.
    induction x; [ discriminate H | ].
    induction x. 
    ++ simpl in H.    
      rewrite <- Nat.compare_eq_iff in H;
      rewrite Nat.compare_succ in H;
      apply Nat.compare_eq_iff in H.
      pose proof Nat.eq_add_0 n (S(n + 0)).
      destruct H0. 
      assert ((n + S (n + 0))%nat = 0). rewrite <- H. reflexivity.
      specialize (H0 H2). destruct H0. rewrite plus_0_r in H3.
      discriminate H3.
    ++ simpl. clear IHx IHx0.
      simpl in H.       
      rewrite <- Nat.compare_eq_iff in H;
      rewrite Nat.compare_succ in H;
      apply Nat.compare_eq_iff in H.
      rewrite plus_comm in H.  rewrite plus_0_r in H.
      rewrite <- Nat.compare_eq_iff in H;
      rewrite Nat.compare_succ in H;
      apply Nat.compare_eq_iff in H. fold Nat.add in H.
      specialize (IHn x).
      assert ((n + n)%nat = (2 * n)%nat). { simpl.  rewrite plus_0_r. reflexivity. }
      rewrite H0 in H. pose proof IHn H. destruct H1.
      split; rewrite <- Nat.compare_eq_iff ;
      rewrite Nat.compare_succ ;
      apply Nat.compare_eq_iff .
      exact H1. exact H2.
Qed.

Lemma ineq2: forall(k0 M: nat),
k0 <= 2 ^ M - 1 -> k0 < 2^M.
Proof.
Admitted.
Lemma ineq3: forall(k0 M: nat),
 2 ^ M - 1 < k0 ->  2^M <= k0.
Proof.
Admitted.
Lemma ineq4:  forall(k M: nat),
 k <= 2 ^ S M - 1 -> k - 2 ^ M <= 2 ^ M - 1.
Proof.
Admitted.
Lemma FFTSplit: forall (x:list C)(M: nat)(a: list C)(b: list C),
(length a = 2^M /\ length b = 2^M /\ 
forall (k: nat), (k <= 2^M - 1) -> Fourier x 0 k (length x) = nth k a (0%R, 0%R)
                        /\ Fourier x 0 (k + 2^M) (length x) = nth k b (0%R, 0%R)) ->
forall (k: nat), (k <= 2^(S M) - 1) -> Fourier x 0 k (length x) = nth k (a++b) (0%R, 0%R).
Proof.
  intros.
  destruct H.
  destruct H1.
  pose proof le_or_lt k  (2 ^ M - 1).
  destruct H3.
  + pose proof H2 _ H3.
    pose proof ineq2 _ _ H3.
    rewrite <- H in H5.
    pose proof app_nth1 a b (0%R, 0%R) H5.
    rewrite H6.
    destruct H4. exact H4.
  + 
    pose proof ineq3 _ _ H3.
    assert (k >= 2 ^ M).

    {unfold ">=". exact H4. }
    rewrite <- H in H5.
    pose proof app_nth2 a b (0%R, 0%R) H5.
    rewrite H6.
    pose proof ineq4 _ _ H0.
    pose proof H2 (k - 2 ^ M)%nat H7.
    rewrite H.
    destruct H8.
    rewrite plus_comm in H9. rewrite <- le_plus_minus in H9.
    exact H9. exact H4.
Qed.

Lemma nthListOp: forall (l1: list C) (l2: list C) (Op: C->C->C) (default: list C) (k: nat) (default0: C),
nth k (ListOp l1 l2 Op default) default0 = Op (nth k l1 default0) (nth k l2 default0).
Proof.
  intros.
  
Admitted.

Lemma PhaseGenLength: forall (n m: nat),
length (PhaseGen n m) = n.
Proof.
  intros.
  induction n.
  + reflexivity.
  + simpl. rewrite app_length. simpl.
    rewrite plus_comm. simpl.
    rewrite <- Nat.compare_eq_iff;
    rewrite Nat.compare_succ;
    rewrite Nat.compare_eq_iff.
    exact IHn.
Qed.

Lemma PhaseLength: forall (N: nat),
length (Phase N) = N.
Proof.
  unfold Phase.
  intros.
  apply PhaseGenLength.
Qed.



Lemma FFTLength: forall(M: nat)(x: list C),
length x = 2 ^ M -> length (FFT x M) = 2 ^ M.
Proof.
  induction M.
  + simpl. intros. exact H.
  + intros. simpl. rewrite app_length. 
    pose proof PhaseLength (2 ^ M).
    pose proof IHM (OddList x). 
    pose proof IHM (EvenList x).
    pose proof EOListLength (2^M) x.
    assert(length x = (2 * 2 ^ M)%nat  ).
    { simpl. simpl in H. rewrite H. reflexivity. }
    specialize (H3 H4); clear H4. 
    destruct H3.
    specialize (H1 H4); clear H4.
    specialize (H2 H3); clear H3.
    rewrite <- H0 in H1, H2.
    pose proof ListOpLength (Phase (2 ^ M)) (FFT (OddList x) M) Cmult [].
    pose proof ListOpLength (Phase (2 ^ M)) (FFT (EvenList x) M) Cmult [].
    assert (length (Phase (2 ^ M)) = length (FFT (OddList x) M) ). rewrite H1; reflexivity.
    assert (length (Phase (2 ^ M)) = length (FFT (EvenList x) M) ). rewrite H2; reflexivity.
    specialize (H3 H5); specialize(H4 H6).
    rewrite <- H1 in H3; rewrite <- H2 in H4.
    pose proof ListOpLength (FFT (EvenList x) M) (ListOp (Phase (2 ^ M)) (FFT (OddList x) M) Cmult []) Cplus [].
    pose proof ListOpLength (FFT (EvenList x) M) (ListOp (Phase (2 ^ M)) (FFT (OddList x) M) Cmult []) Cminus [].
    rewrite H3 in H7, H8. rewrite <- H5, H6 in H7, H8. 
    assert (length (FFT (EvenList x) M) = length (FFT (EvenList x) M) ). reflexivity.
    specialize (H7 H9). rewrite H7.
    specialize (H8 H9). rewrite H8.
    rewrite H2 H0. rewrite plus_0_r. reflexivity.
Qed.

Lemma Length: forall (M: nat)(x: list C)(Op : C -> C -> C),
length x = 2 ^ (S M) ->
length
  (ListOp (FFT (EvenList x) M) (ListOp (Phase (2 ^ M)) (FFT (OddList x) M) Cmult []) Op []) =
2 ^ M.
Proof.
    intros.
    pose proof PhaseLength (2 ^ M).
    pose proof EOListLength (2^M) x.
    assert( length x = (2 * 2 ^ M)%nat  ).
    { simpl. simpl in H. rewrite H. reflexivity. }
    specialize (H1 H2); clear H2.
    destruct H1.
    pose proof FFTLength M (EvenList x) H1.
    pose proof FFTLength M (OddList x) H2.
    pose proof ListOpLength (Phase (2 ^ M)) (FFT (OddList x) M) Cmult [].
    assert (length (Phase (2 ^ M)) = length (FFT (OddList x) M) ). rewrite H4 H0. reflexivity.
    specialize(H5 H6).
    pose proof ListOpLength (FFT (EvenList x) M) (ListOp (Phase (2 ^ M)) (FFT (OddList x) M) Cmult []) Op [].
    rewrite H5 H3 H0 in H7.
    assert (2 ^ M = 2 ^ M). reflexivity.
    specialize (H7 H8). rewrite H7.
    reflexivity.
Qed.

Lemma PhaseGen_k: forall(n k m: nat),
k < n -> nth k (PhaseGen n m) (0%R, 0%R) = exp_complex (-2 * PI * INR k * / INR (m)).
Proof.
  induction n.
  + intros. pose proof lt_n_0 k. contradiction.
  + intros. pose proof lt_n_Sm_le k n. specialize (H0 H).
      pose proof le_lt_or_eq k n. specialize(H1 H0). destruct H1.
      ++ specialize (IHn k m H1). simpl. 
            pose proof PhaseGenLength n m.
            rewrite <- H2 in H1.
            pose proof app_nth1 (PhaseGen n m) ([exp_complex (-2 * PI*INR n  / INR m)]) (0%R, 0%R) H1.
            rewrite H3. exact IHn.
      ++ simpl. pose proof PhaseGenLength n m. rewrite <- H2 in H1.
            pose proof le_refl k.
            assert (k >= length (PhaseGen n m)).
            { unfold ">=". rewrite <- H1. exact H3. }
            pose proof app_nth2 (PhaseGen n m) ([exp_complex (-  2 * PI * INR n/ INR m)]) (0%R, 0%R) H4.
            rewrite H5. rewrite <- H1. rewrite minus_diag. simpl.
            rewrite H1. rewrite H2. reflexivity.
Qed.

Lemma Phase_k: forall(k : nat) (M: nat),
k < 2 ^ M -> nth k (Phase (2 ^ M)) (0%R, 0%R) = exp_complex (-2 * PI * INR k * / (INR (2 * 2 ^ M))).
Proof.
  intros.
  unfold Phase.
  apply PhaseGen_k.
  exact H.
Qed.

Lemma ineq: forall(k0: nat) (M: nat),
2^(S M - 1) - 1 < (k0 + 2 ^ (S M - 1)).
Proof.
Admitted.


Lemma eq0: forall M,
(2 * INR (2 ^ M))%R = (INR (2 * 2 ^ M)).
Proof.
Admitted.

(**  This is our ultimate goal.*)
Definition FFTCorrect : forall (M:nat) (x:list C) (k:nat),
  (length x = 2 ^ M /\ k <= 2 ^ M - 1) -> 
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
    ++ simpl. rewrite Length. exact H. pose proof minus_n_O M. reflexivity.
    ++ split. rewrite Length. exact H. pose proof minus_n_O M. simpl. reflexivity.
          split.
    +++ repeat rewrite nthListOp. 
          assert (M = (S M - 1)%nat). { simpl. rewrite <- minus_n_O. reflexivity. } rewrite H1 in H0. clear H1.
          pose proof FstHalf x k0 (2^(S M - 1)) H0.
          rewrite H. simpl; rewrite Nat.add_0_r. 
          simpl in H1; rewrite Nat.sub_0_r in H1. rewrite Nat.add_0_r in H1. 
          pose proof IHM (EvenList x) k0. pose proof IHM (OddList x) k0.
          pose proof EOListLength _ _ H. fold Nat.pow in H4. destruct H4.
          simpl in H0; rewrite Nat.sub_0_r in H0. 
          assert(Fourier (EvenList x) 0 k0 (length (EvenList x)) = nth k0 (FFT (EvenList x) M) (0%R, 0%R)).
          apply H2. split. exact H4. exact H0.
          assert(Fourier (OddList x) 0 k0 (length (OddList x)) = nth k0 (FFT (OddList x) M) (0%R, 0%R)).
          apply H3. split. exact H5. exact H0.
          pose proof ineq2 k0 M H0.
          pose proof Phase_k k0 M.
          pose proof H9 H8.
          rewrite H10. rewrite H1. rewrite <- H6. rewrite <- H7. rewrite H4 H5. rewrite eq0. 
          reflexivity.
    +++ repeat rewrite nthListOp. 
          pose proof ineq k0 M.
          pose proof SndHalf x (k0 + 2 ^ (S M - 1)) (2^(S M - 1)) .
          rewrite H. simpl in H1; rewrite Nat.sub_0_r in H1; rewrite plus_comm in H1.
          simpl in H2; rewrite Nat.sub_0_r in H2; rewrite Nat.add_0_r in H2.
          rewrite plus_comm in H2. rewrite minus_plus in H2.
          pose proof IHM (EvenList x) k0. pose proof IHM (OddList x) k0.
          pose proof EOListLength _ _ H. fold Nat.pow in H5. destruct H5.
          simpl in H0. 
          assert(Fourier (EvenList x) 0 k0 (length (EvenList x)) = nth k0 (FFT (EvenList x) M) (0%R, 0%R)).
          apply H3. split. exact H5. exact H0.
          assert(Fourier (OddList x) 0 k0 (length (OddList x)) = nth k0 (FFT (OddList x) M) (0%R, 0%R)).
          apply H4. split. exact H6. exact H0.
          pose proof Phase_k k0 M.
          pose proof H2 H1.
          rewrite H5 in H7; rewrite H6 in H8; rewrite H7 H8 in H10; rewrite H9.
          apply ineq2. exact H0.
          simpl; rewrite Nat.add_0_r. rewrite plus_comm.
          rewrite H10. rewrite eq0. simpl. rewrite Nat.add_0_r.
          reflexivity. 
Qed.
