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

Require Import Coq.Lists.List.

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

Definition lenX_pow_2_n_1 (X : list C) : Prop :=
  exists N, Datatypes.length X = Init.Nat.pow 2 N.
(* equal of nat *)

Definition lenX_pow_2_n_2 (X : list C) : Prop :=
  exists N, Z.of_nat (Datatypes.length X) = Z.pow 2 N.
(* equal of Z *)

(* This is Fourier transform *)
Fixpoint Fourier (X : list C) (n : R) (k : Z) (len : nat) : C :=
  match X with
    | nil => (0%R , 0%R)
    | (x :: X')%list => x * (exp_complex (-2 * PI * n * (IZR k) / (INR len ))) + (Fourier X' (n + 1) k len)
  end.

(* This is the even term of the Fourier transform *)
Fixpoint Fourier_even (X : list C) (n : R) (k : Z) (len : nat) : C :=
  match X with
    | nil => (0%R , 0%R)
    | (x :: X')%list => x * (exp_complex (-2 * PI * 2 * n * (IZR k) / (2 * (INR len) ))) + (Fourier_even X' (n + 1) k len)
  end.

(* This is the odd term of the Fourier transform *)
Fixpoint Fourier_odd (X : list C) (n : R) (k : Z) (len : nat) : C :=
  match X with
    | nil => (0%R , 0%R)
    | (x :: X')%list => x * (exp_complex (-2 * PI * (2 * n + 1) * (IZR k) / (2 * (INR len) ))) + (Fourier_odd X' (n + 1) k len)
  end.

(* Split Fourier transform into odd and even when k < N / 2*)
Lemma Fourier_split1: forall (X : list C) (k : Z),
  ~(X = nil) ->
  exists len, len = Datatypes.length X ->
  exists len', len = (2 * len')%nat ->
  Fourier X 0 k len = Fourier_even (EvenList X) 0 k len' + Fourier_odd (EvenList X) 0 k len'.
Proof.
Admitted.

Lemma Fourier_split2_1: forall (X : list C) (k : Z),
  ~(X = nil) ->
  exists len, len = Datatypes.length X ->
  Fourier_even X 0 k len = Fourier X 0 k len.
Proof.
Admitted.

Lemma Fourier_split2_2: forall (X : list C) (k : Z),
  ~(X = nil) ->
  exists len, len = Datatypes.length X ->
  Fourier_odd X 0 k len = (exp_complex (-2 * PI * (IZR k ) / (2 * (INR len)) )) * Fourier X 0 k len.
Proof.
Admitted.

(* Split Fourier transform into odd and even when k < N / 2*)
Lemma Fourier_split3_1: forall (X : list C) (k : Z),
  ~(X = nil) ->
  exists len, len = Datatypes.length X ->
  exists k', k' = (k - Z.of_nat len / 2)%Z ->
  Fourier_even X 0 k len = Fourier X 0 k' len.
Proof.
Admitted.

Lemma Fourier_split3_2: forall (X : list C) (k : Z),
  ~(X = nil) ->
  exists len, len = Datatypes.length X ->
  Fourier_odd X 0 k len = (exp_complex (-2 * PI * (IZR k) / (2 * INR len) )) * Fourier X 0 k len.
Proof.
Admitted.


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
  simpl.
  lia.
Qed.

Lemma example4: forall (x y z w : C) , lenX_pow_2_n_2 [x; y; z; w].
Proof.
  intros.
  unfold lenX_pow_2_n_2.
  exists 2.
  simpl.
  lia.
Qed.


(*Pointwise operation on two complex lists. Used in FFT*)
Fixpoint ListOp (l1: list C) (l2: list C) (Op: C->C->C) (default: list C): list C :=
  match l1, l2 with
     | nil, nil => nil
     | (x1 :: l1' ), (x2 :: l2') => (Op x1 x2) :: ListOp l1' l2' Op default
     | nil, _ => default
     | _, nil => default 
  end.


Example ListOpexample: forall (x y z w : C) , ListOp [x;y] [z;w] Cplus [] = [x+z; y+w].
Proof.
  intros.
  simpl.
  reflexivity.
Qed.
 
(* Generating the phase factor used in FFT.*)
Fixpoint PhaseGen (n:nat) (m: nat): list C :=
match n with
| O => [(1%R,0%R)]
| S n' => PhaseGen n' m ++ [(exp_complex (-(IZR (Z.of_nat n)) * 2 * PI / (IZR (Z.of_nat m))))]
end.

Definition Phase (N: nat): list C:= PhaseGen N (2*N).

(* The length of list x must be 2^M. *)
Fixpoint FFT (x:list C) (M:nat): list C :=
  match M with
  | O => x
  | S M' => ListOp (FFT (EvenList x) M') (ListOp (FFT (OddList x) M') (Phase (2^M')) Cmult []) Cplus [] 
                  ++ ListOp (FFT (EvenList x) M') (ListOp (FFT (OddList x) M') (Phase (2^M')) Cmult []) Cminus []
  end.


Example FFTEx: FFT [ (1%R,0%R) ; (2%R,0%R) ]  1%nat = [(3%R, 0%R); ( (-1)%R,0%R)].
Proof.
  unfold FFT.
  unfold EvenList, OddList.
  unfold ListOp. simpl.
  unfold Cmult, Cplus. simpl. 
  simpl. 
  compute.
Admitted.


