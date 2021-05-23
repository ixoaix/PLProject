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

Print pow_2_n.
(* pow_2_n = fun n : nat => (2 ^ n)%R
     : nat -> R *)
Print Zpower.two_power_nat.
(* Zpower.two_power_nat = 
fun n : nat => Z.pos (Zpower.shift_nat n 1)
     : nat -> Z *)
Print Init.Nat.pow.
(* Init.Nat.pow = 
fix pow (n m : nat) {struct m} : nat :=
  match m with
  | 0 => 1
  | S m0 => (n * pow n m0)%nat
  end
     : nat -> nat -> nat *)
Print Nat.pow.
(* Nat.pow = 
fix pow (n m : nat) {struct m} : nat :=
  match m with
  | 0 => 1
  | S m0 => (n * pow n m0)%nat
  end
     : nat -> nat -> nat *)
Print INR.
(* INR = 
fix INR (n : nat) : R :=
  match n with
  | 0 => 0%R
  | 1 => 1%R
  | S (S _ as n0) => (INR n0 + 1)%R
  end
     : nat -> R *)
Print Int_part.
(* Int_part = fun r : R => (up r - 1)%Z
     : R -> Z *)
Print Z.of_nat.
(* Z.of_nat = 
fun n : nat =>
match n with
| 0 => 0%Z
| S n0 => Z.pos (Pos.of_succ_nat n0)
end
     : nat -> Z *)
Print Datatypes.length.
(* length: forall [A : Type], list A -> nat *)
Print Z.pow.
(* Z.pow = 
fun x y : Z =>
match y with
| 0 => 1
| Z.pos p => Z.pow_pos x p
| Z.neg _ => 0
end
     : Z -> Z -> Z *)

Definition exp_complex (x : nat) : C :=
  (cos_n x, sin_n x).

Definition lenX_pow_2_n_1 (X : list C) : Prop :=
  exists n, Z.of_nat (Datatypes.length X) = Zpower.two_power_nat n.
(* equal of Z *)

Definition lenX_pow_2_n_2 (X : list C) : Prop :=
  exists n, Datatypes.length X = Init.Nat.pow 2 n.
(* equal of nat *)

Definition lenX_pow_2_n_3 (X : list C) : Prop :=
  exists n, Z.of_nat (Datatypes.length X) = Z.pow 2 n.
(* equal of Z *)

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
  reflexivity.
Qed.

Lemma example5: forall (x y z w : C) , lenX_pow_2_n_3 [x; y; z; w].
Proof.
  intros.
  unfold lenX_pow_2_n_3.
  exists 2.
  simpl.
  reflexivity.
Qed.

Fixpoint X_len2pow (X : list C) : list C :=
  match (lenX_pow_2_n_3 X) with
    | True => X
    | False => X_len2pow (X ++ (0, 0)::nil)
  end.
