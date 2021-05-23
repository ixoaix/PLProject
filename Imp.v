(** (This following part of this file is copied from <<Software Foundation>>
volume 1. It should be only used for lecture notes and homework assignments for
course CS263 of Shanghai Jiao Tong University, 2019 spring. Any other usage are
not allowed. For the material of thses parts, please refer to the original
book.) *)

(*******************************************)
(*************** Coqlib ********************)
(*******************************************)

Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Export Coq.micromega.Psatz.
Require Export Coq.ZArith.ZArith.
Require Export Coq.Strings.String.
Require Export Coq.Logic.Classical.
Require Import PL.RTClosure.

Arguments clos_refl_trans {A} _ _ _.
Arguments clos_refl_trans_1n {A} _ _ _.
Arguments clos_refl_trans_n1 {A} _ _ _.

Open Scope Z.

Module Func.

Definition add {A: Type} (f g: A -> Z): A -> Z :=
  fun a => f a + g a.

Definition sub {A: Type} (f g: A -> Z): A -> Z :=
  fun a => f a - g a.

Definition mul {A: Type} (f g: A -> Z): A -> Z :=
  fun a => f a * g a.

Definition test_eq {A: Type} (f g: A -> Z): A -> Prop :=
  fun a => f a = g a.

Definition test_le {A: Type} (f g: A -> Z): A -> Prop :=
  fun a => f a <= g a.

Definition equiv {A: Type} (f g: A -> Z): Prop :=
  forall a, f a = g a.

Definition le {A: Type} (f g: A -> Z): Prop :=
  forall a, f a <= g a.

End Func.

Module Sets.

Definition full {A: Type}: A -> Prop := fun _ => True.

Definition empty {A: Type}: A -> Prop := fun _ => False.

Definition intersect {A: Type} (X Y: A -> Prop) := fun a => X a /\ Y a.

Definition complement {A: Type} (X: A -> Prop) := fun a => ~ X a.

Definition equiv {A: Type} (X Y: A -> Prop): Prop :=
  forall a, X a <-> Y a.

End Sets.

Declare Scope func_scop.
Delimit Scope func_scope with Func.

Notation "f + g" := (Func.add f g): func_scope.
Notation "f - g" := (Func.sub f g): func_scope.
Notation "f * g" := (Func.mul f g): func_scope.

Lemma Func_equiv_refl: forall A, Reflexive (@Func.equiv A).
Proof.
  intros.
  unfold Reflexive.
  unfold Func.equiv.
  intros.
  reflexivity.
Qed.

Lemma Func_equiv_sym: forall A, Symmetric (@Func.equiv A).
Proof.
  intros.
  unfold Symmetric.
  unfold Func.equiv.
  intros.
  rewrite H.
  reflexivity.
Qed.

Lemma Func_equiv_trans: forall A, Transitive (@Func.equiv A).
Proof.
  intros.
  unfold Transitive.
  unfold Func.equiv.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma Sets_equiv_refl: forall A, Reflexive (@Sets.equiv A).
Proof.
  intros.
  unfold Reflexive.
  unfold Sets.equiv.
  intros.
  tauto.
Qed.

Lemma Sets_equiv_sym: forall A, Symmetric (@Sets.equiv A).
Proof.
  intros.
  unfold Symmetric.
  unfold Sets.equiv.
  intros.
  rewrite H.
  reflexivity.
Qed.

Lemma Sets_equiv_trans: forall A, Transitive (@Sets.equiv A).
Proof.
  intros.
  unfold Transitive.
  unfold Sets.equiv.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma Func_add_equiv: forall A,
  Proper (@Func.equiv A ==> @Func.equiv A ==> @Func.equiv A) Func.add.
Proof.
  intros.
  unfold Proper, respectful.
  intros f1 f2 ? g1 g2 ?.
  unfold Func.equiv in H.
  unfold Func.equiv in H0.
  unfold Func.equiv.
  intros.
  unfold Func.add.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma Func_sub_equiv: forall A,
  Proper (@Func.equiv A ==> @Func.equiv A ==> @Func.equiv A) Func.sub.
Proof.
  intros.
  unfold Proper, respectful.
  intros f1 f2 ? g1 g2 ?.
  unfold Func.equiv in H.
  unfold Func.equiv in H0.
  unfold Func.equiv.
  intros.
  unfold Func.sub.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma Func_mul_equiv: forall A,
  Proper (@Func.equiv A ==> @Func.equiv A ==> @Func.equiv A) Func.mul.
Proof.
  intros.
  unfold Proper, respectful.
  intros f1 f2 ? g1 g2 ?.
  unfold Func.equiv in H.
  unfold Func.equiv in H0.
  unfold Func.equiv.
  intros.
  unfold Func.mul.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma Func_test_eq_equiv: forall A,
  Proper (@Func.equiv A ==> @Func.equiv A ==> @Sets.equiv A) Func.test_eq.
Proof.
  unfold Proper, respectful.
  unfold Func.equiv, Sets.equiv, Func.test_eq.
  intros A f1 f2 ? g1 g2 ?.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma Func_test_le_equiv: forall A,
  Proper (@Func.equiv A ==> @Func.equiv A ==> @Sets.equiv A) Func.test_le.
Proof.
  unfold Proper, respectful.
  unfold Func.equiv, Sets.equiv, Func.test_le.
  intros A f1 f2 ? g1 g2 ?.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma Sets_intersect_equiv: forall A,
  Proper (@Sets.equiv A ==> @Sets.equiv A ==> @Sets.equiv A) Sets.intersect.
Proof.
  unfold Proper, respectful.
  unfold Sets.equiv, Sets.intersect.
  intros A S1 S2 ? T1 T2 ?.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma Sets_complement_equiv: forall A,
  Proper (@Sets.equiv A ==> @Sets.equiv A) Sets.complement.
Proof.
  unfold Proper, respectful.
  unfold Sets.equiv, Sets.complement.
  intros A S1 S2 ?.
  intros.
  rewrite H.
  reflexivity.
Qed.

Lemma Sets_complement_complement: forall A (S: A -> Prop),
  Sets.equiv (Sets.complement (Sets.complement S)) S.
Proof.
  intros.
  unfold Sets.equiv, Sets.complement.
  intros.
  tauto.
Qed.

Existing Instances Func_equiv_refl
                   Func_equiv_sym
                   Func_equiv_trans
                   Func_add_equiv
                   Func_sub_equiv
                   Func_mul_equiv.

Existing Instances Sets_equiv_refl
                   Sets_equiv_sym
                   Sets_equiv_trans
                   Func_test_eq_equiv
                   Func_test_le_equiv
                   Sets_intersect_equiv
                   Sets_complement_equiv.

Module BinRel.

Definition id {A: Type}: A -> A -> Prop := fun a b => a = b.

Definition empty {A B: Type}: A -> B -> Prop := fun a b => False.

Definition concat {A B C: Type} (r1: A -> B -> Prop) (r2: B -> C -> Prop): A -> C -> Prop :=
  fun a c => exists b, r1 a b /\ r2 b c.

Definition filter1 {A B: Type} (f: A -> Prop): A -> B -> Prop :=
  fun a b => f a.

Definition filter2 {A B: Type} (f: B -> Prop): A -> B -> Prop :=
  fun a b => f b.

Definition union {A B: Type} (r1 r2: A -> B -> Prop): A -> B -> Prop :=
  fun a b => r1 a b \/ r2 a b.

Definition intersection {A B: Type} (r1 r2: A -> B -> Prop): A -> B -> Prop :=
  fun a b => r1 a b /\ r2 a b.

Definition omega_union {A B: Type} (rs: nat -> A -> B -> Prop): A -> B -> Prop :=
  fun st1 st2 => exists n, rs n st1 st2.

Definition test_rel {A} (X: A -> Prop): A -> A -> Prop :=
  fun st1 st2 => st1 = st2 /\ X st1.

Definition equiv {A B: Type} (r1 r2: A -> B -> Prop): Prop :=
  forall a b, r1 a b <-> r2 a b.

Definition le {A B: Type} (r1 r2: A -> B -> Prop): Prop :=
  forall a b, r1 a b -> r2 a b.

End BinRel.

Lemma Rel_equiv_refl: forall A B, Reflexive (@BinRel.equiv A B).
Proof.
  unfold Reflexive, BinRel.equiv.
  intros.
  reflexivity.
Qed.

Lemma Rel_equiv_sym: forall A B, Symmetric (@BinRel.equiv A B).
Proof.
  unfold Symmetric, BinRel.equiv.
  intros.
  rewrite H.
  reflexivity.
Qed.

Lemma Rel_equiv_trans: forall A B, Transitive (@BinRel.equiv A B).
Proof.
  unfold Transitive, BinRel.equiv.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma Rel_equiv_test_rel: forall A,
  Proper (@Sets.equiv A ==> @BinRel.equiv A A) BinRel.test_rel.
Proof.
  unfold Proper, respectful.
  unfold Sets.equiv, BinRel.equiv, BinRel.test_rel.
  intros A X Y ?.
  intros.
  rewrite H.
  reflexivity.
Qed.

Lemma Rel_equiv_concat: forall A,
  Proper (@BinRel.equiv A A ==> @BinRel.equiv A A ==> @BinRel.equiv A A) BinRel.concat.
Proof.
  unfold Proper, respectful.
  unfold BinRel.equiv, BinRel.concat.
  intros A X1 X2 ? Y1 Y2 ?.
  intros a c.
  unfold iff.
  split.
  + intros [b [? ?]].
    exists b.
    rewrite <- H, <- H0.
    tauto.
  + intros [b [? ?]].
    exists b.
    rewrite H, H0.
    tauto.
Qed.

Lemma Rel_equiv_union: forall A,
  Proper (@BinRel.equiv A A ==> @BinRel.equiv A A ==> @BinRel.equiv A A) BinRel.union.
Proof.
  unfold Proper, respectful.
  unfold BinRel.equiv, BinRel.union.
  intros A X1 X2 ? Y1 Y2 ?.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma Rel_equiv_omega_union: forall A B (r1 r2: nat -> A -> B -> Prop),
  (forall n, BinRel.equiv (r1 n) (r2 n)) ->
  BinRel.equiv (BinRel.omega_union r1) (BinRel.omega_union r2).
Proof.
  unfold BinRel.equiv, BinRel.omega_union.
  intros.
  unfold iff; split; intros HH;
  destruct HH as [n ?]; exists n.
  + rewrite <- H.
    exact H0.
  + rewrite H.
    exact H0.
Qed.

Lemma Rel_equiv_Rel_le: forall A B (r1 r2: A -> B -> Prop),
  BinRel.equiv r1 r2 <-> BinRel.le r1 r2 /\ BinRel.le r2 r1.
Proof.
  unfold BinRel.equiv, BinRel.le.
  intros.
  unfold iff at 1.
  split; intros.
  + split; intros ? ?; rewrite H; tauto.
  + destruct H.
    unfold iff; split.
    - apply H.
    - apply H0.
Qed.

Lemma union_comm: forall A B (r1 r2: A -> B -> Prop),
  BinRel.equiv (BinRel.union r1 r2) (BinRel.union r2 r1).
Proof.
  intros.
  unfold BinRel.equiv, BinRel.union.
  intros.
  tauto.
Qed.

Lemma Rel_concat_assoc:
  forall A B C D (R1: A -> B -> Prop) (R2: B -> C -> Prop) (R3: C -> D -> Prop),
  BinRel.equiv
    (BinRel.concat (BinRel.concat R1 R2) R3)
    (BinRel.concat R1 (BinRel.concat R2 R3)).
Proof.
  unfold BinRel.equiv, BinRel.concat.
  intros; split; intros.
  + destruct H as [b' [[a' [? ?]] ?]].
    exists a'.
    split; [tauto |].
    exists b'.
    tauto.
  + destruct H as [a' [? [b' [? ?]]]].
    exists b'.
    split; [| tauto].
    exists a'.
    tauto.
Qed.

Existing Instances Rel_equiv_refl
                   Rel_equiv_sym
                   Rel_equiv_trans
                   Rel_equiv_test_rel
                   Rel_equiv_concat
                   Rel_equiv_union.

(*******************************************)
(*************** Syntax ********************)
(*******************************************)

Definition var: Type := nat.

Inductive aexp : Type :=
  | ANum (n : Z)
  | AId (X : var)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Coercion ANum : Z >-> aexp.

Definition bool_to_bexp (b : bool) : bexp :=
  if b then BTrue else BFalse.
Coercion bool_to_bexp : bool >-> bexp.

Bind Scope imp_scope with aexp.
Bind Scope imp_scope with bexp.
Delimit Scope imp_scope with imp.

Notation "x + y" := (APlus x y) (at level 50, left associativity) : imp_scope.
Notation "x - y" := (AMinus x y) (at level 50, left associativity) : imp_scope.
Notation "x * y" := (AMult x y) (at level 40, left associativity) : imp_scope.
Notation "x <= y" := (BLe x y) (at level 70, no associativity) : imp_scope.
Notation "x == y" := (BEq x y) (at level 70, no associativity) : imp_scope.
Notation "x && y" := (BAnd x y) (at level 40, left associativity) : imp_scope.
Notation "'!' b" := (BNot b) (at level 39, right associativity) : imp_scope.

Inductive com : Type :=
  | CSkip
  | CAss (X: var) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

Bind Scope imp_scope with com.
Notation "'Skip'" :=
   CSkip : imp_scope.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity) : imp_scope.
Notation "'While' b 'Do' c 'EndWhile'" :=
  (CWhile b c) (at level 80, right associativity) : imp_scope.
Notation "'If' c1 'Then' c2 'Else' c3 'EndIf'" :=
  (CIf c1 c2 c3) (at level 10, right associativity) : imp_scope.

Module Abstract_Pretty_Printing.
Coercion AId: var >-> aexp.
Notation "x '::=' a" :=
  (CAss x a) (at level 80) : imp_scope.
End Abstract_Pretty_Printing.

Definition state: Type := nat -> Z.

(*******************************************)
(************ Denotations ******************)
(*******************************************)

Definition constant_func {A: Type} (c: Z): A -> Z := fun _ => c.
Definition query_var (X: var): state -> Z := fun st => st X.

Fixpoint aeval (a : aexp) : state -> Z :=
  match a with
  | ANum n => constant_func n
  | AId X => query_var X
  | APlus a1 a2 => (aeval a1 + aeval a2)%Func
  | AMinus a1 a2  => (aeval a1 - aeval a2)%Func
  | AMult a1 a2 => (aeval a1 * aeval a2)%Func
  end.

Fixpoint beval (b : bexp) : state -> Prop :=
  match b with
  | BTrue       => Sets.full
  | BFalse      => Sets.empty
  | BEq a1 a2   => Func.test_eq (aeval a1) (aeval a2)
  | BLe a1 a2   => Func.test_le (aeval a1) (aeval a2)
  | BNot b1     => Sets.complement (beval b1)
  | BAnd b1 b2  => Sets.intersect (beval b1 ) (beval b2)
  end.

Definition if_sem
  (b: bexp)
  (then_branch else_branch: state -> state -> Prop)
  : state -> state -> Prop
:=
  BinRel.union
    (BinRel.concat (BinRel.test_rel (beval b)) then_branch)
    (BinRel.concat (BinRel.test_rel (beval (BNot b))) else_branch).

Fixpoint iter_loop_body (b: bexp)
                        (loop_body: state -> state -> Prop)
                        (n: nat): state -> state -> Prop :=
  match n with
  | O =>
         BinRel.test_rel (beval (BNot b))
  | S n' =>
         BinRel.concat
           (BinRel.test_rel (beval b))
           (BinRel.concat
              loop_body
              (iter_loop_body b loop_body n'))
  end.

Definition loop_sem (b: bexp) (loop_body: state -> state -> Prop):
  state -> state -> Prop :=
  BinRel.omega_union (iter_loop_body b loop_body).

Fixpoint ceval (c: com): state -> state -> Prop :=
  match c with
  | CSkip => BinRel.id
  | CAss X E =>
      fun st1 st2 =>
        st2 X = aeval E st1 /\
        forall Y, X <> Y -> st1 Y = st2 Y
  | CSeq c1 c2 => BinRel.concat (ceval c1) (ceval c2)
  | CIf b c1 c2 => if_sem b (ceval c1) (ceval c2)
  | CWhile b c => loop_sem b (ceval c)
  end.

Lemma ceval_CSkip: ceval CSkip = BinRel.id.
Proof. intros. simpl. reflexivity. Qed.

Lemma ceval_CAss: forall X E,
  ceval (CAss X E) =
    fun st1 st2 =>
      st2 X = aeval E st1 /\
        forall Y, X <> Y -> st1 Y = st2 Y.
Proof. intros. simpl. reflexivity. Qed.

Lemma ceval_CSeq: forall c1 c2,
  ceval (c1 ;; c2) = BinRel.concat (ceval c1) (ceval c2).
Proof. intros. simpl. reflexivity. Qed.

Lemma ceval_CIf: forall b c1 c2,
  ceval (CIf b c1 c2) = if_sem b (ceval c1) (ceval c2).
Proof. intros. simpl. reflexivity. Qed.

Lemma ceval_CWhile: forall b c,
  ceval (While b Do c EndWhile) = loop_sem b (ceval c).
Proof. intros. simpl. reflexivity. Qed.

Arguments ceval: simpl never.

Definition aexp_equiv (a1 a2: aexp): Prop :=
  Func.equiv (aeval a1) (aeval a2).

Lemma aexp_equiv_refl: Reflexive aexp_equiv.
Proof.
  unfold Reflexive, aexp_equiv.
  intros.
  reflexivity.
Qed.

Lemma aexp_equiv_sym: Symmetric aexp_equiv.
Proof.
  unfold Symmetric, aexp_equiv.
  intros.
  rewrite H.
  reflexivity.
Qed.

Lemma aexp_equiv_trans: Transitive aexp_equiv.
Proof.
  unfold Transitive, aexp_equiv.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma APlus_congr:
  Proper (aexp_equiv ==> aexp_equiv ==> aexp_equiv) APlus.
Proof.
  unfold Proper, respectful.
  unfold aexp_equiv.
  intros a1 a1' ? a2 a2' ?.
  simpl.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma AMinus_congr:
  Proper (aexp_equiv ==> aexp_equiv ==> aexp_equiv) AMinus.
Proof.
  unfold Proper, respectful.
  unfold aexp_equiv.
  intros a1 a1' ? a2 a2' ?.
  simpl.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma AMult_congr:
  Proper (aexp_equiv ==> aexp_equiv ==> aexp_equiv) AMult.
Proof.
  unfold Proper, respectful.
  unfold aexp_equiv.
  intros a1 a1' ? a2 a2' ?.
  simpl.
  rewrite H, H0.
  reflexivity.
Qed.

Existing Instances aexp_equiv_refl
                   aexp_equiv_sym
                   aexp_equiv_trans
                   APlus_congr
                   AMinus_congr
                   AMult_congr.

Definition bexp_equiv (b1 b2: bexp): Prop :=
  Sets.equiv (beval b1) (beval b2).

Lemma bexp_equiv_refl: Reflexive bexp_equiv.
Proof.
  unfold Reflexive, bexp_equiv.
  intros.
  reflexivity.
Qed.

Lemma bexp_equiv_sym: Symmetric bexp_equiv.
Proof.
  unfold Symmetric, bexp_equiv.
  intros.
  rewrite H.
  reflexivity.
Qed.

Lemma bexp_equiv_trans: Transitive bexp_equiv.
Proof.
  unfold Transitive, bexp_equiv.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma BEq_congr:
  Proper (aexp_equiv ==> aexp_equiv ==> bexp_equiv) BEq.
Proof.
  unfold Proper, respectful.
  unfold aexp_equiv, bexp_equiv.
  intros; simpl.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma BLe_congr:
  Proper (aexp_equiv ==> aexp_equiv ==> bexp_equiv) BLe.
Proof.
  unfold Proper, respectful.
  unfold aexp_equiv, bexp_equiv.
  intros; simpl.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma BAnd_congr:
  Proper (bexp_equiv ==> bexp_equiv ==> bexp_equiv) BAnd.
Proof.
  unfold Proper, respectful.
  unfold bexp_equiv.
  intros; simpl.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma BNot_congr: Proper (bexp_equiv ==> bexp_equiv) BNot.
Proof.
  unfold Proper, respectful.
  unfold bexp_equiv.
  intros; simpl.
  rewrite H.
  reflexivity.
Qed.

Existing Instances bexp_equiv_refl
                   bexp_equiv_sym
                   bexp_equiv_trans
                   BEq_congr
                   BLe_congr
                   BAnd_congr
                   BNot_congr.

Definition com_equiv (c1 c2: com): Prop :=
  BinRel.equiv (ceval c1) (ceval c2).

Lemma com_equiv_refl: Reflexive com_equiv.
Proof.
  unfold Reflexive, com_equiv.
  intros.
  reflexivity.
Qed.

Lemma com_equiv_sym: Symmetric com_equiv.
Proof.
  unfold Symmetric, com_equiv.
  intros.
  rewrite H.
  reflexivity.
Qed.

Lemma com_equiv_trans: Transitive com_equiv.
Proof.
  unfold Transitive, com_equiv.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma CAss_congr: forall (X: var),
  Proper (aexp_equiv ==> com_equiv) (CAss X).
Proof.
  unfold Proper, respectful.
  unfold aexp_equiv, com_equiv, BinRel.equiv.
  intros X E E' ?.
  intros st1 st2.
  rewrite ! ceval_CAss.
  unfold Func.equiv in H.
  specialize (H st1).
  rewrite H.
  reflexivity.
Qed.

Lemma CSeq_congr: Proper (com_equiv ==> com_equiv ==> com_equiv) CSeq.
Proof.
  unfold Proper, respectful.
  unfold com_equiv.
  intros c1 c1' ? c2 c2' ?.
  rewrite ! ceval_CSeq.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma CIf_congr:
  Proper (bexp_equiv ==> com_equiv ==> com_equiv ==> com_equiv) CIf.
Proof.
  unfold Proper, respectful.
  unfold bexp_equiv, com_equiv.
  intros b b' ? c1 c1' ? c2 c2' ?.
  rewrite ! ceval_CIf.
  unfold if_sem.
  simpl.
  rewrite H, H0, H1.
  reflexivity.
Qed.

Lemma CWhile_congr:
  Proper (bexp_equiv ==> com_equiv ==> com_equiv) CWhile.
Proof.
  unfold Proper, respectful.
  unfold bexp_equiv, com_equiv.
  intros b b' ? c c' ?.
  rewrite ! ceval_CWhile.
  unfold loop_sem.
  apply Rel_equiv_omega_union.
  intros.
  induction n; simpl.
  + rewrite H.
    reflexivity.
  + rewrite IHn, H, H0.
    reflexivity.
Qed.

Lemma loop_sem_unrolling: forall b (R: state -> state -> Prop),
  BinRel.equiv (loop_sem b R) (if_sem b (BinRel.concat R (loop_sem b R)) BinRel.id).
Proof.
  intros.
  unfold BinRel.equiv; intros st1 st2.
  unfold iff; split; intros.
  + unfold loop_sem, BinRel.omega_union in H.
    destruct H as [n ?].
    destruct n.
    - simpl in H.
      unfold if_sem, BinRel.union.
      right; simpl.
      unfold BinRel.concat, BinRel.id.
      exists st2; split; [exact H | reflexivity].
    - simpl in H.
      unfold if_sem, BinRel.union.
      left.
      unfold BinRel.concat in H.
      unfold BinRel.concat.
      destruct H as [st1' [? [st1'' [? ?]]]].
      exists st1'; split; [exact H |].
      exists st1''; split; [exact H0 |].
      unfold loop_sem, BinRel.omega_union.
      exists n.
      exact H1.
  + unfold if_sem, union in H.
    unfold loop_sem, BinRel.omega_union.
    destruct H.
    2: {
      exists 0%nat.
      simpl.
      unfold BinRel.concat, BinRel.id in H.
      destruct H as [st2' [? ?]].
      rewrite H0 in H; exact H.
    }
    unfold BinRel.concat at 1 in H.
    destruct H as [st1' [? ?]].
    unfold BinRel.concat in H0.
    destruct H0 as [st0 [? ?]].
    unfold loop_sem, BinRel.omega_union in H1.
    destruct H1 as [n ?].
    exists (S n).
    simpl.
    unfold BinRel.concat at 1.
    exists st1'; split; [exact H |].
    unfold BinRel.concat.
    exists st0; split; [exact H0 | exact H1].
Qed.

Theorem loop_unrolling : forall b c,
  com_equiv
    (While b Do c EndWhile)
    (If b Then (c ;; While b Do c EndWhile) Else Skip EndIf).
Proof.
  intros.
  unfold com_equiv.
  rewrite ceval_CIf, ceval_CSeq, ceval_CSkip.
  rewrite ceval_CWhile.
  apply loop_sem_unrolling.
Qed.

Lemma seq_assoc : forall c1 c2 c3,
  com_equiv ((c1;;c2);;c3) (c1;;(c2;;c3)).
Proof.
  intros.
  unfold com_equiv.
  rewrite ! ceval_CSeq.
  apply Rel_concat_assoc.
Qed.

(*******************************************)
(************* Small Step ******************)
(*******************************************)

Inductive aexp_halt: aexp -> Prop :=
  | AH_num : forall n, aexp_halt (ANum n).

Inductive astep : state -> aexp -> aexp -> Prop :=
  | AS_Id : forall st X,
      astep st
        (AId X) (ANum (st X))

  | AS_Plus1 : forall st a1 a1' a2,
      astep st
        a1 a1' ->
      astep st
        (APlus a1 a2) (APlus a1' a2)
  | AS_Plus2 : forall st a1 a2 a2',
      aexp_halt a1 ->
      astep st
        a2 a2' ->
      astep st
        (APlus a1 a2) (APlus a1 a2')
  | AS_Plus : forall st n1 n2,
      astep st
        (APlus (ANum n1) (ANum n2)) (ANum (n1 + n2))

  | AS_Minus1 : forall st a1 a1' a2,
      astep st
        a1 a1' ->
      astep st
        (AMinus a1 a2) (AMinus a1' a2)
  | AS_Minus2 : forall st a1 a2 a2',
      aexp_halt a1 ->
      astep st
        a2 a2' ->
      astep st
        (AMinus a1 a2) (AMinus a1 a2')
  | AS_Minus : forall st n1 n2,
      astep st
        (AMinus (ANum n1) (ANum n2)) (ANum (n1 - n2))

  | AS_Mult1 : forall st a1 a1' a2,
      astep st
        a1 a1' ->
      astep st
        (AMult a1 a2) (AMult a1' a2)
  | AS_Mult2 : forall st a1 a2 a2',
      aexp_halt a1 ->
      astep st
        a2 a2' ->
      astep st
        (AMult a1 a2) (AMult a1 a2')
  | AS_Mult : forall st n1 n2,
      astep st
        (AMult (ANum n1) (ANum n2)) (ANum (n1 * n2)).

Inductive bexp_halt: bexp -> Prop :=
  | BH_True : bexp_halt BTrue
  | BH_False : bexp_halt BFalse.

Inductive bstep : state -> bexp -> bexp -> Prop :=

  | BS_Eq1 : forall st a1 a1' a2,
      astep st
        a1 a1' ->
      bstep st
        (BEq a1 a2) (BEq a1' a2)
  | BS_Eq2 : forall st a1 a2 a2',
      aexp_halt a1 ->
      astep st
        a2 a2' ->
      bstep st
        (BEq a1 a2) (BEq a1 a2')
  | BS_Eq_True : forall st n1 n2,
      n1 = n2 ->
      bstep st
        (BEq (ANum n1) (ANum n2)) BTrue
  | BS_Eq_False : forall st n1 n2,
      n1 <> n2 ->
      bstep st
        (BEq (ANum n1) (ANum n2)) BFalse

  | BS_Le1 : forall st a1 a1' a2,
      astep st
        a1 a1' ->
      bstep st
        (BLe a1 a2) (BLe a1' a2)
  | BS_Le2 : forall st a1 a2 a2',
      aexp_halt a1 ->
      astep st
        a2 a2' ->
      bstep st
        (BLe a1 a2) (BLe a1 a2')
  | BS_Le_True : forall st n1 n2,
      n1 <= n2 ->
      bstep st
        (BLe (ANum n1) (ANum n2)) BTrue
  | BS_Le_False : forall st n1 n2,
      n1 > n2 ->
      bstep st
        (BLe (ANum n1) (ANum n2)) BFalse

  | BS_NotStep : forall st b1 b1',
      bstep st
        b1 b1' ->
      bstep st
        (BNot b1) (BNot b1')
  | BS_NotTrue : forall st,
      bstep st
        (BNot BTrue) BFalse
  | BS_NotFalse : forall st,
      bstep st
        (BNot BFalse) BTrue

  | BS_AndStep : forall st b1 b1' b2,
      bstep st
        b1 b1' ->
      bstep st
       (BAnd b1 b2) (BAnd b1' b2)
  | BS_AndTrue : forall st b,
      bstep st
       (BAnd BTrue b) b
  | BS_AndFalse : forall st b,
      bstep st
       (BAnd BFalse b) BFalse.

Section cstep.

Local Open Scope imp.

Inductive cstep : (com * state) -> (com * state) -> Prop :=
  | CS_AssStep : forall st X a a',
      astep st a a' ->
      cstep (CAss X a, st) (CAss X a', st)
  | CS_Ass : forall st1 st2 X n,
      st2 X = n ->
      (forall Y, X <> Y -> st1 Y = st2 Y) ->
      cstep (CAss X (ANum n), st1) (Skip, st2)
  | CS_SeqStep : forall st c1 c1' st' c2,
      cstep (c1, st) (c1', st') ->
      cstep (c1 ;; c2 , st) (c1' ;; c2, st')
  | CS_Seq : forall st c2,
      cstep (Skip ;; c2, st) (c2, st)
  | CS_IfStep : forall st b b' c1 c2,
      bstep st b b' ->
      cstep
        (If b  Then c1 Else c2 EndIf, st)
        (If b'  Then c1 Else c2 EndIf, st)
  | CS_IfTrue : forall st c1 c2,
      cstep (If BTrue Then c1 Else c2 EndIf, st) (c1, st)
  | CS_IfFalse : forall st c1 c2,
      cstep (If BFalse Then c1 Else c2 EndIf, st) (c2, st)
  | CS_While : forall st b c,
      cstep
        (While b Do c EndWhile, st)
        (If b Then (c;; While b Do c EndWhile) Else Skip EndIf, st).

End cstep.

Definition multi_astep (st: state): aexp -> aexp -> Prop := clos_refl_trans (astep st).

Definition multi_bstep (st: state): bexp -> bexp -> Prop := clos_refl_trans (bstep st).

Definition multi_cstep: com * state -> com * state -> Prop := clos_refl_trans cstep.

(*******************************************)
(************* Hoare Logic *****************)
(*************** including decorated prog **)
(*******************************************)

Module Assertion_S.

Inductive term : Type :=
  | TNum (n : Z)
  | TDenote (a : aexp)
  | TPlus (t1 t2 : term)
  | TMinus (t1 t2 : term)
  | TMult (t1 t2 : term)
  .

Coercion TNum : Z >-> term.

Bind Scope term_scope with term.
Delimit Scope term_scope with term.

Notation "x + y" := (TPlus x y) (at level 50, left associativity) : term_scope.
Notation "x - y" := (TMinus x y) (at level 50, left associativity) : term_scope.
Notation "x * y" := (TMult x y) (at level 40, left associativity) : term_scope.
Notation "{[ a ]}" := (TDenote ((a)%imp)) (at level 30, no associativity) : term_scope.

Inductive Assertion : Type :=
  | DLe (t1 t2 : term)
  | DLt (t1 t2 : term)
  | DEq (t1 t2 : term)
  | DInj (b: bexp)
  | DProp (P: Prop)
  | DOr (d1 d2 : Assertion)
  | DAnd (d1 d2 : Assertion)
  | DNot (d: Assertion)
  | DExists (d: Z -> Assertion)
  | DForall (d: Z -> Assertion).

Coercion DProp : Sortclass >-> Assertion.
Bind Scope assert_scope with Assertion.
Delimit Scope assert_scope with assert.

Notation "x <= y" := (DLe ((x)%term) ((y)%term)) (at level 70, no associativity) : assert_scope.
Notation "x '<' y" := (DLt ((x)%term) ((y)%term)) (at level 70, no associativity) : assert_scope.
Notation "x = y" := (DEq ((x)%term) ((y)%term)) (at level 70, no associativity) : assert_scope.
Notation "{[ b ]}" := (DInj ((b)%imp)) (at level 30, no associativity) : assert_scope.
Notation "x 'OR' y" := (DOr x y) (at level 76, left associativity) : assert_scope.
Notation "x 'AND' y" := (DAnd x y) (at level 74, left associativity) : assert_scope.
Notation "'NOT' x" := (DNot x) (at level 73, right associativity) : assert_scope.
Notation "'EXISTS' x ',' d " := (DExists (fun x: Z => ((d)%assert))) (at level 77, x ident, right associativity) : assert_scope.
Notation "'FORALL' x ',' d " := (DForall (fun x: Z => ((d)%assert))) (at level 77, x ident, right associativity) : assert_scope.

Definition eqb_compute: nat -> nat -> bool :=
  fix eqb (n m : nat) {struct n} : bool :=
  match n with
  | 0%nat => match m with
             | 0%nat => true
             | S _ => false
             end
  | S n' => match m with
            | 0%nat => false
            | S m' => eqb n' m'
            end
  end.

Section subst.

Variable X: var.
Variable a: aexp.

Fixpoint aexp_sub (a0: aexp): aexp :=
    match a0 with
    | ANum n => ANum n
    | AId X' =>
         if eqb_compute X X'
         then a
         else @AId X'
    | APlus a1 a2 => APlus (aexp_sub a1) (aexp_sub a2)
    | AMinus a1 a2 => AMinus (aexp_sub a1) (aexp_sub a2)
    | AMult a1 a2 => AMult (aexp_sub a1) (aexp_sub a2)
    end.

Fixpoint bexp_sub (b: bexp): bexp :=
    match b with
    | BTrue => BTrue
    | BFalse => BFalse
    | BEq a1 a2 => BEq (aexp_sub a1) (aexp_sub a2)
    | BLe a1 a2 => BLe (aexp_sub a1) (aexp_sub a2)
    | BNot b => BNot (bexp_sub b)
    | BAnd b1 b2 => BAnd (bexp_sub b1) (bexp_sub b2)
    end.

Fixpoint term_sub (t: term) :=
    match t with
    | TNum n => TNum n
    | TDenote a => TDenote (aexp_sub a)
    | TPlus t1 t2 => TPlus (term_sub t1) (term_sub t2)
    | TMinus t1 t2 => TMinus (term_sub t1) (term_sub t2)
    | TMult t1 t2 => TMult (term_sub t1) (term_sub t2)
    end.

Fixpoint assn_sub (d: Assertion): Assertion :=
    match d with
    | DLe t1 t2 => DLe (term_sub t1) (term_sub t2)
    | DLt t1 t2 => DLt (term_sub t1) (term_sub t2)
    | DEq t1 t2 => DEq (term_sub t1) (term_sub t2)
    | DInj b => DInj (bexp_sub b)
    | DProp P => DProp P
    | DOr d1 d2 => DOr (assn_sub d1) (assn_sub d2)
    | DAnd d1 d2 => DAnd (assn_sub d1) (assn_sub d2)
    | DNot d => DNot (assn_sub d)
    | DExists d => DExists (fun z: Z => assn_sub (d z))
    | DForall d => DForall (fun z: Z => assn_sub (d z))
    end.

End subst.

Definition aexp_denote (st: state) (a: aexp): Z :=
  aeval a st.

Definition bexp_denote (st: state) (b: bexp): Prop :=
  beval b st.

Fixpoint term_denote (st: state) (t: term): Z :=
  match t with
  | TNum n => n
  | TDenote a => aexp_denote st a
  | TPlus t1 t2 => (term_denote st t1) + (term_denote st t2)
  | TMinus t1 t2 => (term_denote st t1) - (term_denote st t2)
  | TMult t1 t2 => (term_denote st t1) * (term_denote st t2)
  end.

Fixpoint Assertion_denote (st: state) (d: Assertion): Prop :=
  match d with
  | DLe t1 t2 => (term_denote st t1) <= (term_denote st t2)
  | DLt t1 t2 => (term_denote st t1) < (term_denote st t2)
  | DEq t1 t2 => (term_denote st t1) = (term_denote st t2)
  | DInj b => bexp_denote st b
  | DProp P => P
  | DOr d1 d2 => (Assertion_denote st d1) \/ (Assertion_denote st d2)
  | DAnd d1 d2 => (Assertion_denote st d1) /\ (Assertion_denote st d2)
  | DNot d => ~ (Assertion_denote st d)
  | DExists d => exists k, Assertion_denote st (d k)
  | DForall d => forall k, Assertion_denote st (d k)
  end.

Definition derives: Assertion -> Assertion -> Prop :=
  fun d1 d2: Assertion =>
  (forall st, Assertion_denote st d1 -> Assertion_denote st d2).

Opaque derives.

Definition equiv_assert (P Q: Assertion): Prop :=
  derives P Q /\ derives Q P.

Parameter hoare_triple: Assertion -> com -> Assertion -> Prop.

Notation "P '|--' Q" :=
  (derives ((P)%assert) ((Q)%assert)) (at level 90, no associativity).

Notation "P '--||--' Q" :=
  (equiv_assert P Q) (at level 90, no associativity).

Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level).

Theorem FOL_complete: forall d1 d2: Assertion,
  (forall st, Assertion_denote st d1 -> Assertion_denote st d2) ->
  d1 |-- d2.
Proof.
  intros.
  exact H.
Qed.

Section simpl.

Fixpoint aexp_simpl (a: aexp): term :=
    match a with
    | ANum n => TNum n
    | AId X => TDenote (AId X)
    | APlus a1 a2 => TPlus (aexp_simpl a1) (aexp_simpl a2)
    | AMinus a1 a2 => TMinus (aexp_simpl a1) (aexp_simpl a2)
    | AMult a1 a2 => TMult (aexp_simpl a1) (aexp_simpl a2)
    end.

Fixpoint bexp_simpl (b: bexp): Assertion :=
    match b with
    | BTrue => DProp True
    | BFalse => DProp False
    | BEq a1 a2 => DEq (aexp_simpl a1) (aexp_simpl a2)
    | BLe a1 a2 => DLe (aexp_simpl a1) (aexp_simpl a2)
    | BNot b => DNot (bexp_simpl b)
    | BAnd b1 b2 => DAnd (bexp_simpl b1) (bexp_simpl b2)
    end.

Fixpoint term_simpl (t: term) :=
    match t with
    | TNum n => TNum n
    | TDenote a => aexp_simpl a
    | TPlus t1 t2 => TPlus (term_simpl t1) (term_simpl t2)
    | TMinus t1 t2 => TMinus (term_simpl t1) (term_simpl t2)
    | TMult t1 t2 => TMult (term_simpl t1) (term_simpl t2)
    end.

Fixpoint assn_simpl (d: Assertion): Assertion :=
    match d with
    | DLe t1 t2 => DLe (term_simpl t1) (term_simpl t2)
    | DLt t1 t2 => DLt (term_simpl t1) (term_simpl t2)
    | DEq t1 t2 => DEq (term_simpl t1) (term_simpl t2)
    | DInj b => bexp_simpl b
    | DProp P => DProp P
    | DOr d1 d2 => DOr (assn_simpl d1) (assn_simpl d2)
    | DAnd d1 d2 => DAnd (assn_simpl d1) (assn_simpl d2)
    | DNot d => DNot (assn_simpl d)
    | DExists d => DExists (fun z: Z => assn_simpl (d z))
    | DForall d => DForall (fun z: Z => assn_simpl (d z))
    end.

Inductive elim_trivial_ex: Assertion -> Assertion -> Prop :=
  | elim_trivial_ex_kernal:
      forall d d': Assertion,
        elim_trivial_ex d d' ->
        elim_trivial_ex (DExists (fun z: Z => d)) d'
  | elim_trivial_ex_ex':
      forall d d': Z -> Assertion,
        (forall z, elim_trivial_ex (d z) (d' z)) ->
        elim_trivial_ex (DExists d) (DExists d')
  | elim_trivial_ex_all':
      forall d d': Z -> Assertion,
        (forall z, elim_trivial_ex (d z) (d' z)) ->
        elim_trivial_ex (DForall d) (DForall d')
  | elim_trivial_ex_or:
      forall d1 d2 d1' d2': Assertion,
        elim_trivial_ex d1 d1' ->
        elim_trivial_ex d2 d2' ->
        elim_trivial_ex (DOr d1 d2) (DOr d1' d2')
  | elim_trivial_ex_and:
      forall d1 d2 d1' d2': Assertion,
        elim_trivial_ex d1 d1' ->
        elim_trivial_ex d2 d2' ->
        elim_trivial_ex (DAnd d1 d2) (DAnd d1' d2')
  | elim_trivial_ex_not:
      forall d d': Assertion,
        elim_trivial_ex d d' ->
        elim_trivial_ex (DNot d) (DNot d')
  | elim_trivial_ex_atom:
      forall d: Assertion,
        elim_trivial_ex d d.

Lemma elim_trivial_ex_ex:
      forall d d': Z -> Assertion,
        (forall z, exists d'', elim_trivial_ex (d z) d'' /\ d'' = d' z) ->
        elim_trivial_ex (DExists d) (DExists d').
Proof.
  intros.
  eapply elim_trivial_ex_ex'.
  intros z; specialize (H z).
  destruct H as [d'' [? ?]].
  subst.
  exact H.
Qed.

Lemma elim_trivial_ex_all:
      forall d d': Z -> Assertion,
        (forall z, exists d'', elim_trivial_ex (d z) d'' /\ d'' = d' z) ->
        elim_trivial_ex (DForall d) (DForall d').
Proof.
  intros.
  eapply elim_trivial_ex_all'.
  intros z; specialize (H z).
  destruct H as [d'' [? ?]].
  subst.
  exact H.
Qed.

End simpl.

Axiom simpl_derives: forall P Q,
  P |-- Q <-> assn_simpl P |-- assn_simpl Q.

Axiom simpl_triple: forall P c Q,
  {{P}} c {{Q}} <-> {{assn_simpl P}} c {{assn_simpl Q}}.

Axiom elim_trivial_ex_derives: forall P Q P' Q',
  elim_trivial_ex P P' -> elim_trivial_ex Q  Q' -> (P |-- Q <-> P' |-- Q').

Axiom elim_trivial_ex_triple: forall P c Q P' Q',
  elim_trivial_ex P P' -> elim_trivial_ex Q  Q' -> ({{P}} c {{Q}} <-> {{P'}} c {{Q'}}).

End Assertion_S.

Module Concrete_Pretty_Printing.
Export Assertion_S.

Class var {var_name: var}: Type :=
  var_name_trivial: var_name = var_name.

Ltac new_var_tac n :=
  first [ try (assert (@var n) by (typeclasses eauto); fail 1);
          exact (eq_refl: @var n); fail 100
        | new_var_tac constr:(S n)].

Notation "'new_var()'" := ltac:(new_var_tac 0%nat).

Definition AId {var_name} (X: @var var_name): aexp := AId var_name.

Coercion AId : var >-> aexp.

Definition CAss {var_name} (v : @var var_name) (a : aexp): com :=
  CAss var_name a.

Notation "x '::=' a" :=
  (CAss x a) (at level 80) : imp_scope.

Definition aexp_sub {var_name} (X: @var var_name) a a0 := aexp_sub var_name a a0.

Definition bexp_sub {var_name} (X: @var var_name) a b := bexp_sub var_name a b.

Definition term_sub {var_name} (X: @var var_name) a t := term_sub var_name a t.

Definition assn_sub {var_name} (X: @var var_name) a d := assn_sub var_name a d.

Arguments aexp_sub {var_name} (X) (a) (a0): simpl never.
Arguments bexp_sub {var_name} (X) (a) (b): simpl never.
Arguments term_sub {var_name} (X) (a) (t): simpl never.
Arguments assn_sub {var_name} (X) (a) (d): simpl never.

Notation "d [ X |-> a ]" := (assn_sub X a ((d)%assert)) (at level 10, X at next level) : assert_scope.
Notation "a0 [ X |-> a ]" := (aexp_sub X a ((a0)%imp)) (at level 10, X at next level) : imp_scope.

Inductive dec: bool -> bool -> Type :=
  | DCEnd (a: Assertion): dec true false
  | DCSeq_A {f1 f2} (a: Assertion) (c: dec f1 f2): dec true f2
  | DCSeq_C {f1 f2} (c1: dcom) (c: dec f1 f2): dec false true

with decorated: Type :=
  | DCBegin (c: dec true true)

with dcom : Type :=
  | DCSkip : dcom
  | DCAss : forall {var_name: nat}, @var var_name -> aexp -> dcom
  | DCIf : bexp -> decorated -> decorated -> dcom
  | DCWhile : bexp -> decorated -> dcom.

Delimit Scope dcom_scope with dcom.
Bind Scope dcom_scope with dcom.
Bind Scope dcom_scope with dec.
Bind Scope dcom_scope with decorated.

Notation "'Skip'" :=
   DCSkip : dcom_scope.
Notation "x '::=' a" :=
  (DCAss x a%imp) (at level 80) : dcom_scope.
Notation "'While' b 'Do' c 'EndWhile'" :=
  (DCWhile b c) (at level 80, right associativity) : dcom_scope.
Notation "'If' c1 'Then' c2 'Else' c3 'EndIf'" :=
  (DCIf c1 c2 c3) (at level 10, right associativity) : dcom_scope.
Notation "c1 '*/' '/*' c2" :=
  (@DCSeq_A true _ c1 c2) (at level 80, right associativity) : dcom_scope.
Notation "c1 ';;' '/*' c2" :=
  (@DCSeq_C true true c1 c2) (at level 80, right associativity) : dcom_scope.
Notation "c1 '/*' c2" :=
  (@DCSeq_C true false c1 c2) (at level 80, right associativity) : dcom_scope.
Notation "c1 '*/' c2" :=
  (@DCSeq_A false _ c1 c2) (at level 80, right associativity) : dcom_scope.
Notation "c1 ';;' c2" :=
  (@DCSeq_C false true c1 c2) (at level 80, right associativity) : dcom_scope.
Notation "c '*/'" := (DCEnd c) (at level 80, right associativity) : dcom_scope.
Notation "'/*' c" := (DCBegin c) (at level 80, right associativity) : dcom_scope.

Module sample_decorated_program.

Local Open Scope dcom_scope.

Local Instance X: var := new_var().
Local Instance Y: var := new_var().

Definition dc1 (m n: Z) : decorated :=
  /* 0 <= m */
  X ::= m;;
  Y ::= 0;;
  /* n * {[Y]} + {[X]} = m AND 0 <= {[X]} */
  While n <= X Do
    /* n * {[Y]} + {[X]} = m AND 0 <= {[X]} AND {[n <= X]} */
    X ::= X - n;;
    Y ::= Y + 1
    /* n * {[Y]} + {[X]} = m AND 0 <= {[X]} */
  EndWhile
  /* n * {[Y]} + {[X]} = m AND 0 <= {[X]} AND NOT {[n <= X]} */
  /* n * {[Y]} + {[X]} = m AND 0 <= {[X]} AND {[X]} < n */.

Definition dc2 (m n: Z) : decorated :=
  /* 0 <= m */
  X ::= m;;
  /* EXISTS x, 0 <= m AND {[X]} = m */
  /* 0 <= m AND {[X]} = m */
  Y ::= 0;;
  /* EXISTS y, 0 <= m AND {[X]} = m AND {[Y]} = 0 */
  /* n * {[Y]} + {[X]} = m AND 0 <= {[X]} */
  While n <= X Do
    /* n * {[Y]} + {[X]} = m AND 0 <= {[X]} AND {[n <= X]} */
    X ::= X - n;;
    /* EXISTS x, n * {[Y]} + {[x]} = m AND 0 <= {[x]} AND
                 {[n <= x]} AND {[X]} = {[x - n]} */
    /* EXISTS x, n * {[Y]} + x = m AND 0 <= x AND
                 n <= x AND {[X]} = x - n */
    /* n * {[Y]} + {[X]} + n = m AND 0 <= {[X]} */
    Y ::= Y + 1
    /* EXISTS y, n * {[y]} + {[X]} + n = m AND 0 <= {[X]} AND
                 {[Y]} = {[y + 1]} */
    /* EXISTS y, n * y + {[X]} + n = m AND 0 <= {[X]} AND
                 {[Y]} = y + 1 */
    /* n * {[Y]} + {[X]} = m AND 0 <= {[X]} */
  EndWhile
  /* n * {[Y]} + {[X]} = m AND 0 <= {[X]} AND NOT {[n <= X]} */
  /* n * {[Y]} + {[X]} = m AND 0 <= {[X]} AND {[X]} < n */.

End sample_decorated_program.

End Concrete_Pretty_Printing.

Module slow_minus.
Section slow_minus.
Import Concrete_Pretty_Printing.

Variables m p: Z.

Instance X: var := new_var().
Instance Y: var := new_var().
Instance Z: var := new_var().
Instance W: var := new_var().
Instance ID: var := new_var().

Definition prog: com :=
    X ::= m;;
    Z ::= p;;
    While !(X == 0) Do
      Z ::= Z - 1;;
      X ::= X - 1
    EndWhile.

Definition prog2: com :=
    X ::= X + Y;;
    Y ::= X - Y;;
    X ::= X - Y.

Definition prog3: com :=
  If X <= Y
  Then Z ::= X - Y
  Else If X <= Y
       Then Skip
       Else Z ::= Y - X
       EndIf
  EndIf.

End slow_minus.
End slow_minus.

Module Assertion_S_Tac.

Export Assertion_S.

Tactic Notation "assert_subst" :=
  unfold Concrete_Pretty_Printing.assn_sub, Concrete_Pretty_Printing.aexp_sub;
  simpl assn_sub;
  simpl aexp_sub;
  repeat match goal with
         | |- context [AId ?var_name] =>
              change (AId ?var_name)
              with (@Concrete_Pretty_Printing.AId var_name _)
             end.

Tactic Notation "assert_subst" "in" constr(H) :=
  unfold Concrete_Pretty_Printing.assn_sub, Concrete_Pretty_Printing.aexp_sub in H;
  simpl assn_sub in H;
  simpl aexp_sub in H;
  repeat match type of H with
         | context [AId ?var_name] =>
              change (AId ?var_name)
              with (@Concrete_Pretty_Printing.AId var_name _) in H
             end.

Ltac assert_simpl_concl :=
  match goal with
  | |- {{ _ }} _ {{ _ }} =>
      rewrite simpl_triple;
      simpl assn_simpl
  | |- _ |-- _ =>
      rewrite simpl_derives;
      simpl assn_simpl
  end;
  repeat match goal with
         | |- context [AId ?var_name] =>
              change (AId ?var_name)
              with (@Concrete_Pretty_Printing.AId var_name _)
             end.

Ltac assert_simpl_assu H :=
  match type of H with
  | {{ _ }} _ {{ _ }} =>
      rewrite simpl_triple in H;
      simpl assn_simpl in H
  | _ |-- _ =>
      rewrite simpl_derives in H;
      simpl assn_simpl in H
  end;
  repeat match type of H with
         | context [AId ?var_name] =>
              change (AId ?var_name)
              with (@Concrete_Pretty_Printing.AId var_name _) in H
             end.

Ltac solve_elim_trivial_ex :=
  idtac;
  first
  [ simple eapply elim_trivial_ex_kernal; solve_elim_trivial_ex
  | simple eapply elim_trivial_ex_ex;
    let x := fresh "x" in intro x;
    eexists; split; [solve_elim_trivial_ex |];
    match goal with
    | |- ?P = _ =>
         let P' := fresh "P" in
         let P' := eval pattern x in P in
         change P with P';
         reflexivity
    end
  | simple eapply elim_trivial_ex_all;
    let x := fresh "x" in intro x;
    eexists; split; [solve_elim_trivial_ex |];
    match goal with
    | |- ?P = _ =>
         let P' := fresh "P" in
         let P' := eval pattern x in P in
         change P with P';
         reflexivity
    end
  | simple apply elim_trivial_ex_or; solve_elim_trivial_ex
  | simple apply elim_trivial_ex_and; solve_elim_trivial_ex
  | simple apply elim_trivial_ex_not; solve_elim_trivial_ex
  | simple apply elim_trivial_ex_atom ].

Ltac elim_trivial_ex_concl :=
  match goal with
  | |- {{ _ }} _ {{ _ }} =>
      erewrite elim_trivial_ex_triple;
      [ | solve_elim_trivial_ex ..]
  | |- _ |-- _ =>
      erewrite elim_trivial_ex_derives;
      [ | solve_elim_trivial_ex ..]
  end.

Ltac elim_trivial_ex_assu H :=
  match type of H with
  | {{ _ }} _ {{ _ }} =>
      erewrite elim_trivial_ex_triple in H;
      [ | solve_elim_trivial_ex ..]
  | _ |-- _ =>
      erewrite elim_trivial_ex_derives in H;
      [ | solve_elim_trivial_ex ..]
  end.

Tactic Notation "assert_simpl" := assert_simpl_concl; elim_trivial_ex_concl.
Tactic Notation "assert_simpl" "in" constr(H) := assert_simpl_assu H; elim_trivial_ex_assu H.

Ltac entailer :=
  match goal with
  | |- _ |-- _ => idtac
  | _ => fail "The proof goal's conclusion is not an assertion derivation."
  end;
  assert_simpl;
  apply FOL_complete;
  let st := fresh "st" in
  intros st;
  cbv [Assertion_denote term_denote];
  repeat
    match goal with
    | |- context [aexp_denote st (Concrete_Pretty_Printing.AId ?X)] =>
           let X' := fresh X "'" in
           set (X' := aexp_denote st (Concrete_Pretty_Printing.AId X));
           clearbody X';
           revert X'
    end;
  first [ clear st | fail 1 "This is not a concrete derivation." ].

End Assertion_S_Tac.

Module Axiomatic_semantics.
Import Concrete_Pretty_Printing.

Axiom hoare_seq : forall (P Q R: Assertion) (c1 c2: com),
  {{P}} c1 {{Q}} ->
  {{Q}} c2 {{R}} ->
  {{P}} c1;;c2 {{R}}.

Axiom hoare_skip : forall P,
  {{P}} Skip {{P}}.

Axiom hoare_if : forall P Q b c1 c2,
  {{ P AND {[b]} }} c1 {{ Q }} ->
  {{ P AND NOT {[b]} }} c2 {{ Q }} ->
  {{ P }} If b Then c1 Else c2 EndIf {{ Q }}.

Axiom hoare_while : forall P b c,
  {{ P AND {[b]} }} c {{P}} ->
  {{P}} While b Do c EndWhile {{ P AND NOT {[b]} }}.

Axiom hoare_asgn_fwd : forall P `(X: var) E,
  {{ P }}
  X ::= E
  {{ EXISTS x, P [X |-> x] AND
               {[X]} = {[ E [X |-> x] ]} }}.

Axiom hoare_consequence : forall (P P' Q Q' : Assertion) c,
  P |-- P' ->
  {{P'}} c {{Q'}} ->
  Q' |-- Q ->
  {{P}} c {{Q}}.

Axiom hoare_asgn_bwd : forall P `(X: var) E,
  {{ P [ X |-> E] }} X ::= E {{ P }}.

End Axiomatic_semantics.

Module Assertion_S_Rules.

Export Assertion_S.

Local Transparent derives.

Lemma AND_left1: forall P Q R: Assertion,
  P |-- R ->
  P AND Q |-- R.
Proof.
  intros.
  intro rho; specialize (H rho).
  simpl.
  tauto.
Qed.

Lemma AND_left2: forall P Q R: Assertion,
  Q |-- R ->
  P AND Q |-- R.
Proof.
  intros.
  intro rho; specialize (H rho).
  simpl.
  tauto.
Qed.

Lemma AND_right: forall P Q R: Assertion,
  P |-- Q ->
  P |-- R ->
  P |-- Q AND R.
Proof.
  intros.
  intro rho; specialize (H rho); specialize (H0 rho).
  simpl.
  tauto.
Qed.

Lemma OR_left: forall P Q R: Assertion,
  P |-- R ->
  Q |-- R ->
  P OR Q |-- R.
Proof.
  intros.
  intro rho; specialize (H rho); specialize (H0 rho).
  simpl.
  tauto.
Qed.

Lemma OR_right1: forall P Q R: Assertion,
  P |-- Q ->
  P |-- Q OR R.
Proof.
  intros.
  intro rho; specialize (H rho).
  simpl.
  tauto.
Qed.

Lemma OR_right2: forall P Q R: Assertion,
  P |-- R ->
  P |-- Q OR R.
Proof.
  intros.
  intro rho; specialize (H rho).
  simpl.
  tauto.
Qed.

Lemma LEM: forall P Q: Assertion,
  P |-- Q OR NOT Q.
Proof.
  intros.
  intro rho.
  simpl.
  tauto.
Qed.

Lemma CONTRA: forall P Q: Assertion,
  P AND NOT P |-- Q.
Proof.
  intros.
  intro rho.
  simpl.
  tauto.
Qed.

Lemma Prop_left: forall (P: Prop) (Q: Assertion),
  ~ P ->
  P |-- Q.
Proof.
  intros.
  intro rho.
  simpl.
  tauto.
Qed.

Lemma Prop_right: forall (P: Assertion) (Q: Prop),
  Q ->
  P |-- Q.
Proof.
  intros.
  intro rho.
  simpl.
  tauto.
Qed.

Lemma False_left: forall (P: Assertion),
  False |-- P.
Proof.
  intros.
  apply Prop_left.
  tauto.
Qed.

Lemma True_right: forall (P: Assertion),
  P |-- True.
Proof.
  intros.
  apply Prop_right.
  tauto.
Qed.

Lemma FORALL_left: forall (P: Z -> Assertion) (Q: Assertion) (x: Z),
  P x |-- Q ->
  FORALL x, P x |-- Q.
Proof.
  intros.
  intro rho.
  simpl.
  firstorder.
Qed.

Lemma FORALL_right: forall (P: Assertion) (Q: Z -> Assertion),
  (forall x, P |-- Q x) ->
  P |-- FORALL x, Q x.
Proof.
  intros.
  intro rho.
  simpl.
  firstorder.
Qed.

Lemma EXISTS_left: forall (P: Z -> Assertion) (Q: Assertion),
  (forall x, P x |-- Q) ->
  EXISTS x, P x |-- Q.
Proof.
  intros.
  intro rho.
  simpl.
  firstorder.
Qed.

Lemma EXISTS_right: forall (P: Assertion) (Q: Z -> Assertion) (x: Z),
  P |-- Q x ->
  P |-- EXISTS x, Q x.
Proof.
  intros.
  intro rho.
  simpl.
  firstorder.
Qed.

Lemma derives_refl: forall (P: Assertion),
  P |-- P.
Proof.
  intros.
  exact (fun rho H => H).
Qed.

Lemma derives_trans: forall (P Q R: Assertion),
  P |-- Q ->
  Q |-- R ->
  P |-- R.
Proof.
  intros.
  exact (fun rho HH => H0 rho (H rho HH)).
Qed.

End Assertion_S_Rules.

Module Derived_Rules.

Import Concrete_Pretty_Printing.
Import Assertion_S_Rules.
Import Axiomatic_semantics.

Corollary hoare_consequence_pre: forall P P' Q c,
  P |-- P' ->
  {{ P' }} c {{ Q }} ->
  {{ P }} c {{ Q }}.
Proof.
  intros.
  eapply hoare_consequence.
  + exact H.
  + exact H0.
  + apply derives_refl.
Qed.

Corollary hoare_consequence_post: forall P Q Q' c,
  {{ P }} c {{ Q' }} ->
  Q' |-- Q ->
  {{ P }} c {{ Q }}.
Proof.
  intros.
  eapply hoare_consequence.
  + apply derives_refl.
  + exact H.
  + exact H0.
Qed.

Corollary hoare_if_weak : forall P Q b c1 c2,
  {{P}} c1 {{Q}} ->
  {{P}} c2 {{Q}} ->
  {{P}} If b Then c1 Else c2 EndIf {{Q}}.
Proof.
  intros.
  apply hoare_if.
  + eapply hoare_consequence_pre.
    2: { exact H. }
    apply AND_left1.
    apply derives_refl.
  + eapply hoare_consequence_pre.
    2: { exact H0. }
    apply AND_left1.
    apply derives_refl.
Qed.

Corollary hoare_asgn_seq: forall P `(X: var) E c Q,
  {{ EXISTS x, P [X |-> x] AND {[X]} = {[ E [X |-> x] ]} }} c {{ Q }} ->
  {{ P }} X ::= E ;; c {{ Q }}.
Proof.
  intros.
  eapply hoare_seq.
  + apply hoare_asgn_fwd.
  + exact H.
Qed.

Corollary hoare_asgn_conseq: forall P `(X: var) E Q,
  EXISTS x, P [X |-> x] AND {[X]} = {[ E [X |-> x] ]} |-- Q ->
  {{ P }} X ::= E {{ Q }}.
Proof.
  intros.
  eapply hoare_consequence_post.
  + apply hoare_asgn_fwd.
  + exact H.
Qed.

End Derived_Rules.

(*******************************************)
(***** Hoare Logic vs. Denotation **********)
(*******************************************)

Module Assertion_D.
Import Abstract_Pretty_Printing.

Definition logical_var: Type := nat.

Inductive aexp' : Type :=
  | ANum' (t : term)
  | AId' (X: var)
  | APlus' (a1 a2 : aexp')
  | AMinus' (a1 a2 : aexp')
  | AMult' (a1 a2 : aexp')
with term : Type :=
  | TNum (n : Z)
  | TId (x: logical_var)
  | TDenote (a : aexp')
  | TPlus (t1 t2 : term)
  | TMinus (t1 t2 : term)
  | TMult (t1 t2 : term).

Inductive bexp' : Type :=
  | BTrue'
  | BFalse'
  | BEq' (a1 a2 : aexp')
  | BLe' (a1 a2 : aexp')
  | BNot' (b : bexp')
  | BAnd' (b1 b2 : bexp').

Coercion ANum' : term >-> aexp'.
Coercion AId' : var >-> aexp'.
Bind Scope vimp_scope with aexp'.
Bind Scope vimp_scope with bexp'.
Delimit Scope vimp_scope with vimp.

Notation "x + y" := (APlus' x y) (at level 50, left associativity) : vimp_scope.
Notation "x - y" := (AMinus' x y) (at level 50, left associativity) : vimp_scope.
Notation "x * y" := (AMult' x y) (at level 40, left associativity) : vimp_scope.
Notation "x <= y" := (BLe' x y) (at level 70, no associativity) : vimp_scope.
Notation "x == y" := (BEq' x y) (at level 70, no associativity) : vimp_scope.
Notation "x && y" := (BAnd' x y) (at level 40, left associativity) : vimp_scope.
Notation "'!' b" := (BNot' b) (at level 39, right associativity) : vimp_scope.

Coercion TNum : Z >-> term.
Coercion TId: logical_var >-> term.
Bind Scope term_scope with term.
Delimit Scope term_scope with term.

Notation "x + y" := (TPlus x y) (at level 50, left associativity) : term_scope.
Notation "x - y" := (TMinus x y) (at level 50, left associativity) : term_scope.
Notation "x * y" := (TMult x y) (at level 40, left associativity) : term_scope.
Notation "{[ a ]}" := (TDenote ((a)%vimp)) (at level 30, no associativity) : term_scope.

(** Of course, every normal expression is a variable expression. *)

Fixpoint ainj (a: aexp): aexp' :=
  match a with
  | ANum n        => ANum' (TNum n)
  | AId X         => AId' X
  | APlus a1 a2   => APlus' (ainj a1) (ainj a2)
  | AMinus a1 a2  => AMinus' (ainj a1) (ainj a2)
  | AMult a1 a2   => AMult' (ainj a1) (ainj a2)
  end.

Fixpoint binj (b : bexp): bexp' :=
  match b with
  | BTrue       => BTrue'
  | BFalse      => BFalse'
  | BEq a1 a2   => BEq' (ainj a1) (ainj a2)
  | BLe a1 a2   => BLe' (ainj a1) (ainj a2)
  | BNot b1     => BNot' (binj b1)
  | BAnd b1 b2  => BAnd' (binj b1) (binj b2)
  end.

(** The following two lines of [Coercion] definition say that Coq will treat
[a] as [ainj b] and treat [b] a s [binj b] automatically when a variable
expression is needed. *)

Coercion ainj: aexp >-> aexp'.
Coercion binj: bexp >-> bexp'.

Inductive Assertion : Type :=
  | AssnLe (t1 t2 : term)
  | AssnLt (t1 t2 : term)
  | AssnEq (t1 t2 : term)
  | AssnDenote (b: bexp')
  | AssnOr (P1 P2 : Assertion)
  | AssnAnd (P1 P2 : Assertion)
  | AssnImpl (P1 P2 : Assertion)
  | AssnNot (P: Assertion)
  | AssnExists (x: logical_var) (P: Assertion)
  | AssnForall (x: logical_var) (P: Assertion).

Bind Scope assert_scope with Assertion.
Delimit Scope assert_scope with assert.

Notation "x <= y" := (AssnLe ((x)%term) ((y)%term)) (at level 70, no associativity) : assert_scope.
Notation "x '<' y" := (AssnLt ((x)%term) ((y)%term)) (at level 70, no associativity) : assert_scope.
Notation "x = y" := (AssnEq ((x)%term) ((y)%term)) (at level 70, no associativity) : assert_scope.
Notation "{[ b ]}" := (AssnDenote ((b)%vimp)) (at level 30, no associativity) : assert_scope.
Notation "P1 'OR' P2" := (AssnOr P1 P2) (at level 76, left associativity) : assert_scope.
Notation "P1 'AND' P2" := (AssnAnd P1 P2) (at level 74, left associativity) : assert_scope.
Notation "P1 'IMPLY' P2" := (AssnImpl P1 P2) (at level 77, right associativity) : assert_scope.
Notation "'NOT' P" := (AssnNot P) (at level 73, right associativity) : assert_scope.
Notation "'EXISTS' x ',' P " := (AssnExists x ((P)%assert)) (at level 79,  right associativity) : assert_scope.
Notation "'FORALL' x ',' P " := (AssnForall x ((P)%assert)) (at level 79, right associativity) : assert_scope.

Fixpoint aexp_rename (x y: logical_var) (a: aexp'): aexp' :=
    match a with
    | ANum' t => ANum' (term_rename x y t)
    | AId' X => AId' X
    | APlus' a1 a2 => APlus' (aexp_rename x y a1) (aexp_rename x y a2)
    | AMinus' a1 a2 => AMinus' (aexp_rename x y a1) (aexp_rename x y a2)
    | AMult' a1 a2 => AMult' (aexp_rename x y a1) (aexp_rename x y a2)
    end
with term_rename (x y: logical_var) (t: term) :=
    match t with
    | TNum n => TNum n
    | TId x' => 
        if Nat.eq_dec x x'
        then TId y
        else TId x'
    | TDenote a => TDenote (aexp_rename x y a)
    | TPlus t1 t2 => TPlus (term_rename x y t1) (term_rename x y t2)
    | TMinus t1 t2 => TMinus (term_rename x y t1) (term_rename x y t2)
    | TMult t1 t2 => TMult (term_rename x y t1) (term_rename x y t2)
    end.

Fixpoint bexp_rename (x y: logical_var) (b: bexp'): bexp' :=
    match b with
    | BTrue' => BTrue'
    | BFalse' => BFalse'
    | BEq' a1 a2 => BEq' (aexp_rename x y a1) (aexp_rename x y a2)
    | BLe' a1 a2 => BLe' (aexp_rename x y a1) (aexp_rename x y a2)
    | BNot' b => BNot' (bexp_rename x y b)
    | BAnd' b1 b2 => BAnd' (bexp_rename x y b1) (bexp_rename x y b2)
    end.

Fixpoint assn_rename (x y: logical_var) (d: Assertion): Assertion :=
    match d with
    | AssnLe t1 t2    => AssnLe (term_rename x y t1) (term_rename x y t2)
    | AssnLt t1 t2    => AssnLt (term_rename x y t1) (term_rename x y t2)
    | AssnEq t1 t2    => AssnEq (term_rename x y t1) (term_rename x y t2)
    | AssnDenote b    => AssnDenote (bexp_rename x y b)
    | AssnOr P1 P2    => AssnOr (assn_rename x y P1) (assn_rename x y P2)
    | AssnAnd P1 P2   => AssnAnd (assn_rename x y P1) (assn_rename x y P2)
    | AssnImpl P1 P2  => AssnImpl (assn_rename x y P1) (assn_rename x y P2)
    | AssnNot P       => AssnNot (assn_rename x y P)
    | AssnExists x' P => if Nat.eq_dec x x'
                         then AssnExists x' P
                         else AssnExists x' (assn_rename x y P)
    | AssnForall x' P => if Nat.eq_dec x x'
                         then AssnForall x' P
                         else AssnForall x' (assn_rename x y P)
    end.

Fixpoint aexp_max_var (a: aexp'): logical_var :=
    match a with
    | ANum' t => term_max_var t
    | AId' X => O
    | APlus' a1 a2 => max (aexp_max_var a1) (aexp_max_var a2)
    | AMinus' a1 a2 => max (aexp_max_var a1) (aexp_max_var a2)
    | AMult' a1 a2 => max (aexp_max_var a1) (aexp_max_var a2)
    end
with term_max_var (t: term): logical_var :=
    match t with
    | TNum n => O
    | TId x => x
    | TDenote a => aexp_max_var a
    | TPlus t1 t2 => max (term_max_var t1) (term_max_var t2)
    | TMinus t1 t2 => max (term_max_var t1) (term_max_var t2)
    | TMult t1 t2 => max (term_max_var t1) (term_max_var t2)
    end.

Fixpoint bexp_max_var (b: bexp'): logical_var :=
    match b with
    | BTrue' => O
    | BFalse' => O
    | BEq' a1 a2 => max (aexp_max_var a1) (aexp_max_var a2)
    | BLe' a1 a2 => max (aexp_max_var a1) (aexp_max_var a2)
    | BNot' b => bexp_max_var b
    | BAnd' b1 b2 => max (bexp_max_var b1) (bexp_max_var b2)
    end.

Fixpoint assn_max_var (d: Assertion): logical_var :=
    match d with
    | AssnLe t1 t2    => max (term_max_var t1) (term_max_var t2)
    | AssnLt t1 t2    => max (term_max_var t1) (term_max_var t2)
    | AssnEq t1 t2    => max (term_max_var t1) (term_max_var t2)
    | AssnDenote b    => bexp_max_var b
    | AssnOr P1 P2    => max (assn_max_var P1) (assn_max_var P2)
    | AssnAnd P1 P2   => max (assn_max_var P1) (assn_max_var P2)
    | AssnImpl P1 P2  => max (assn_max_var P1) (assn_max_var P2)
    | AssnNot P       => assn_max_var P
    | AssnExists x' P => max x' (assn_max_var P)
    | AssnForall x' P => max x' (assn_max_var P)
    end.

Definition new_var (P: Assertion) (E: aexp'): logical_var :=
  S (max (assn_max_var P) (aexp_max_var E)).

Fixpoint aexp_sub (X: var) (E: aexp') (a: aexp'): aexp' :=
    match a with
    | ANum' t => ANum' (term_sub X E t)
    | AId' X' =>
         if Nat.eq_dec X X'
         then E
         else AId' X'
    | APlus' a1 a2 => APlus' (aexp_sub X E a1) (aexp_sub X E a2)
    | AMinus' a1 a2 => AMinus' (aexp_sub X E a1) (aexp_sub X E a2)
    | AMult' a1 a2 => AMult' (aexp_sub X E a1) (aexp_sub X E a2)
    end
with term_sub (X: var) (E: aexp') (t: term) :=
    match t with
    | TNum n => TNum n
    | TId x => TId x
    | TDenote a => TDenote (aexp_sub X E a)
    | TPlus t1 t2 => TPlus (term_sub X E t1) (term_sub X E t2)
    | TMinus t1 t2 => TMinus (term_sub X E t1) (term_sub X E t2)
    | TMult t1 t2 => TMult (term_sub X E t1) (term_sub X E t2)
    end.

Fixpoint bexp_sub (X: var) (E: aexp') (b: bexp'): bexp' :=
    match b with
    | BTrue' => BTrue'
    | BFalse' => BFalse'
    | BEq' a1 a2 => BEq' (aexp_sub X E a1) (aexp_sub X E a2)
    | BLe' a1 a2 => BLe' (aexp_sub X E a1) (aexp_sub X E a2)
    | BNot' b => BNot' (bexp_sub X E b)
    | BAnd' b1 b2 => BAnd' (bexp_sub X E b1) (bexp_sub X E b2)
    end.

Fixpoint aexp_occur (x: logical_var) (a: aexp'): nat :=
    match a with
    | ANum' t => term_occur x t
    | AId' X => O
    | APlus' a1 a2 => (aexp_occur x a1) + (aexp_occur x a2)
    | AMinus' a1 a2 => (aexp_occur x a1) + (aexp_occur x a2)
    | AMult' a1 a2 => (aexp_occur x a1) + (aexp_occur x a2)
    end
with term_occur (x: logical_var) (t: term): nat :=
    match t with
    | TNum n => O
    | TId x' => if Nat.eq_dec x x' then S O else O
    | TDenote a => aexp_occur x a
    | TPlus t1 t2 => (term_occur x t1) + (term_occur x t2)
    | TMinus t1 t2 => (term_occur x t1) + (term_occur x t2)
    | TMult t1 t2 => (term_occur x t1) + (term_occur x t2)
    end.

Fixpoint bexp_occur (x: logical_var) (b: bexp'): nat :=
    match b with
    | BTrue' => O
    | BFalse' => O
    | BEq' a1 a2 => (aexp_occur x a1) + (aexp_occur x a2)
    | BLe' a1 a2 => (aexp_occur x a1) + (aexp_occur x a2)
    | BNot' b => bexp_occur x b
    | BAnd' b1 b2 => (bexp_occur x b1) + (bexp_occur x b2)
    end.

Fixpoint assn_free_occur (x: logical_var) (d: Assertion): nat :=
    match d with
    | AssnLe t1 t2    => (term_occur x t1) + (term_occur x t2)
    | AssnLt t1 t2    => (term_occur x t1) + (term_occur x t2)
    | AssnEq t1 t2    => (term_occur x t1) + (term_occur x t2)
    | AssnDenote b    => bexp_occur x b
    | AssnOr P1 P2    => (assn_free_occur x P1) + (assn_free_occur x P2)
    | AssnAnd P1 P2   => (assn_free_occur x P1) + (assn_free_occur x P2)
    | AssnImpl P1 P2  => (assn_free_occur x P1) + (assn_free_occur x P2)
    | AssnNot P       => assn_free_occur x P
    | AssnExists x' P => if Nat.eq_dec x x'
                         then O
                         else assn_free_occur x P
    | AssnForall x' P => if Nat.eq_dec x x'
                         then O
                         else assn_free_occur x P
    end.

Fixpoint assn_occur (x: logical_var) (d: Assertion): nat :=
    match d with
    | AssnLe t1 t2    => (term_occur x t1) + (term_occur x t2)
    | AssnLt t1 t2    => (term_occur x t1) + (term_occur x t2)
    | AssnEq t1 t2    => (term_occur x t1) + (term_occur x t2)
    | AssnDenote b    => bexp_occur x b
    | AssnOr P1 P2    => (assn_occur x P1) + (assn_occur x P2)
    | AssnAnd P1 P2   => (assn_occur x P1) + (assn_occur x P2)
    | AssnImpl P1 P2  => (assn_occur x P1) + (assn_occur x P2)
    | AssnNot P       => assn_occur x P
    | AssnExists x' P => if Nat.eq_dec x x'
                         then S (assn_occur x P)
                         else assn_occur x P
    | AssnForall x' P => if Nat.eq_dec x x'
                         then S (assn_occur x P)
                         else assn_occur x P
    end.

Lemma assn_occur_free_occur: forall x P,
  (assn_free_occur x P <= assn_occur x P)%nat.
Proof.
  intros.
  induction P; simpl.
  - apply le_n.
  - apply le_n.
  - apply le_n.
  - apply le_n.
  - apply plus_le_compat; tauto.
  - apply plus_le_compat; tauto.
  - apply plus_le_compat; tauto.
  - exact IHP.
  - destruct (Nat.eq_dec x x0).
    * apply Nat.le_0_l.
    * exact IHP.
  - destruct (Nat.eq_dec x x0).
    * apply Nat.le_0_l.
    * exact IHP.
Qed.

Corollary assn_occur_O: forall x P,
  assn_occur x P = O ->
  assn_free_occur x P = O.
Proof.
  intros.
  pose proof assn_occur_free_occur x P.
  rewrite H in H0.
  inversion H0.
  reflexivity.
Qed.

Fixpoint rename_all (E: aexp') (d: Assertion): Assertion :=
    match d with
    | AssnLe t1 t2   => AssnLe t1 t2
    | AssnLt t1 t2   => AssnLt t1 t2
    | AssnEq t1 t2   => AssnEq t1 t2
    | AssnDenote b   => AssnDenote b
    | AssnOr P1 P2   => AssnOr (rename_all E P1) (rename_all E P2)
    | AssnAnd P1 P2  => AssnAnd (rename_all E P1) (rename_all E P2)
    | AssnImpl P1 P2 => AssnImpl (rename_all E P1) (rename_all E P2)
    | AssnNot P      => AssnNot (rename_all E P)
    | AssnExists x P => match aexp_occur x E with
                        | O => AssnExists x (rename_all E P)
                        | _ => AssnExists
                                 (new_var (rename_all E P) E)
                                 (assn_rename x
                                   (new_var (rename_all E P) E)
                                   (rename_all E P))
                        end
    | AssnForall x P => match aexp_occur x E with
                        | O => AssnForall x (rename_all E P)
                        | _ => AssnForall
                                 (new_var (rename_all E P) E)
                                 (assn_rename x
                                   (new_var (rename_all E P) E)
                                   (rename_all E P))
                        end
    end.

Fixpoint naive_sub (X: var) (E: aexp') (d: Assertion): Assertion :=
    match d with
    | AssnLe t1 t2   => AssnLe (term_sub X E t1) (term_sub X E t2)
    | AssnLt t1 t2   => AssnLt (term_sub X E t1) (term_sub X E t2)
    | AssnEq t1 t2   => AssnEq (term_sub X E t1) (term_sub X E t2)
    | AssnDenote b   => AssnDenote (bexp_sub X E b)
    | AssnOr P1 P2   => AssnOr (naive_sub X E P1) (naive_sub X E P2)
    | AssnAnd P1 P2  => AssnAnd (naive_sub X E P1) (naive_sub X E P2)
    | AssnImpl P1 P2 => AssnImpl (naive_sub X E P1) (naive_sub X E P2)
    | AssnNot P      => AssnNot (naive_sub X E P)
    | AssnExists x P => AssnExists x (naive_sub X E P)
    | AssnForall x P => AssnForall x (naive_sub X E P)
    end.

Definition assn_sub (X: var) (E: aexp') (P: Assertion): Assertion :=
  naive_sub X E (rename_all E P).

Notation "d [ X |-> a ]" := (assn_sub X a ((d)%assert)) (at level 10, X at next level) : assert_scope.
Notation "a0 [ X |-> a ]" := (aexp_sub X a ((a0)%vimp)) (at level 10, X at next level) : vimp_scope.

Inductive hoare_triple: Type :=
| Build_hoare_triple (P: Assertion) (c: com) (Q: Assertion).

Notation "{{ P }}  c  {{ Q }}" :=
  (Build_hoare_triple P c%imp Q) (at level 90, c at next level).

Class FirstOrderLogic: Type := {
  FOL_provable: Assertion -> Prop
}.

Definition derives {T: FirstOrderLogic} (P Q: Assertion): Prop :=
  FOL_provable (P IMPLY Q).

Notation "P '|--' Q" :=
  (derives ((P)%assert) ((Q)%assert)) (at level 90, no associativity).

Inductive provable {T: FirstOrderLogic}: hoare_triple -> Prop :=
  | hoare_seq : forall (P Q R: Assertion) (c1 c2: com),
      provable ({{P}} c1 {{Q}}) ->
      provable ({{Q}} c2 {{R}}) ->
      provable ({{P}} c1;;c2 {{R}})
  | hoare_skip : forall P,
      provable ({{P}} Skip {{P}})
  | hoare_if : forall P Q (b: bexp) c1 c2,
      provable ({{ P AND {[b]} }} c1 {{ Q }}) ->
      provable ({{ P AND NOT {[b]} }} c2 {{ Q }}) ->
      provable ({{ P }} If b Then c1 Else c2 EndIf {{ Q }})
  | hoare_while : forall P (b: bexp) c,
      provable ({{ P AND {[b]} }} c {{P}}) ->
      provable ({{P}} While b Do c EndWhile {{ P AND NOT {[b]} }})
  | hoare_asgn_bwd : forall P (X: var) (E: aexp),
      provable ({{ P [ X |-> E] }} X ::= E {{ P }})
  | hoare_consequence : forall (P P' Q Q' : Assertion) c,
      P |-- P' ->
      provable ({{P'}} c {{Q'}}) ->
      Q' |-- Q ->
      provable ({{P}} c {{Q}}).

Notation "|--  tr" := (provable tr) (at level 91, no associativity).

Definition Lassn: Type := logical_var -> Z.

Definition Lassn_update (La: Lassn) (x: logical_var) (v: Z): Lassn :=
  fun y => if (Nat.eq_dec x y) then v else La y.

Lemma Lassn_update_spec: forall La x v,
  (Lassn_update La x v) x = v /\
  (forall y, x <> y -> La y = (Lassn_update La x v) y).
Proof.
  intros.
  unfold Lassn_update.
  split.
  + destruct (Nat.eq_dec x x).
    - reflexivity.
    - assert (x = x). { reflexivity. }
      tauto.
  + intros.
    destruct (Nat.eq_dec x y).
    - tauto.
    - reflexivity.
Qed.

Definition Interp: Type := state * Lassn.

Definition Interp_Lupdate (J: Interp) (x: logical_var) (v: Z): Interp :=
  (fst J, Lassn_update (snd J) x v).

Fixpoint aexp'_denote (J: Interp) (a: aexp'): Z :=
    match a with
    | ANum' t => term_denote J t
    | AId' X => (fst J) X
    | APlus' a1 a2 => aexp'_denote J a1 + aexp'_denote J a2
    | AMinus' a1 a2 => aexp'_denote J a1 - aexp'_denote J a2
    | AMult' a1 a2 => aexp'_denote J a1 * aexp'_denote J a2
    end
with term_denote (J: Interp) (t: term): Z :=
    match t with
    | TNum n => n
    | TId x => (snd J) x
    | TDenote a => aexp'_denote J a
    | TPlus t1 t2 => term_denote J t1 + term_denote J t2
    | TMinus t1 t2 => term_denote J t1 - term_denote J t2
    | TMult t1 t2 => term_denote J t1 * term_denote J t2
    end.

Fixpoint bexp'_denote (J: Interp) (b: bexp'): Prop :=
    match b with
    | BTrue' => True
    | BFalse' => False
    | BEq' a1 a2 => aexp'_denote J a1 = aexp'_denote J a2
    | BLe' a1 a2 => (aexp'_denote J a1 <= aexp'_denote J a2)%Z
    | BNot' b => ~ bexp'_denote J b
    | BAnd' b1 b2 => bexp'_denote J b1 /\ bexp'_denote J b2
    end.

Fixpoint satisfies (J: Interp) (d: Assertion): Prop :=
    match d with
    | AssnLe t1 t2 => (term_denote J t1 <= term_denote J t2)%Z
    | AssnLt t1 t2 => (term_denote J t1 < term_denote J t2)%Z
    | AssnEq t1 t2 => (term_denote J t1 = term_denote J t2)%Z
    | AssnDenote b => bexp'_denote J b
    | AssnOr P1 P2 => (satisfies J P1) \/ (satisfies J P2)
    | AssnAnd P1 P2 => (satisfies J P1) /\ (satisfies J P2)
    | AssnImpl P1 P2 => ~ (satisfies J P1) \/ (satisfies J P2)
    | AssnNot P => ~ (satisfies J P)
    | AssnExists x P => exists v, satisfies (Interp_Lupdate J x v) P
    | AssnForall x P => forall v, satisfies (Interp_Lupdate J x v) P
    end.

Notation "J  |==  x" := (satisfies J x) (at level 90, no associativity).

Definition valid (Tr: hoare_triple): Prop :=
  match Tr with
  | Build_hoare_triple P c Q =>
      forall La st1 st2,
        (st1, La) |== P -> ceval c st1 st2 -> (st2, La) |== Q
  end.

Notation "|==  Tr" := (valid Tr) (at level 91, no associativity).

Lemma seq_assoc_sound : forall P c1 c2 c3 Q,
  |== {{ P }} c1 ;; c2 ;; c3 {{ Q }} <->
  |== {{ P }} (c1 ;; c2) ;; c3 {{ Q }}.
Proof.
  unfold valid.
  intros.
  pose proof seq_assoc c1 c2 c3.
  unfold com_equiv, BinRel.equiv in H.
  split; intros.
  + specialize (H0 La st1 st2).
    apply H0.
    - exact H1.
    - apply H.
      exact H2.
  + specialize (H0 La st1 st2).
    apply H0.
    - exact H1.
    - apply H.
      exact H2.
Qed.

Lemma aeval_aexp'_denote: forall st La a,
  aeval a st = aexp'_denote (st, La) (ainj a).
Proof.
  intros.
  induction a; simpl.
  + reflexivity.
  + reflexivity.
  + unfold Func.add.
    rewrite IHa1, IHa2.
    reflexivity.
  + unfold Func.sub.
    rewrite IHa1, IHa2.
    reflexivity.
  + unfold Func.mul.
    rewrite IHa1, IHa2.
    reflexivity.
Qed.

Lemma beval_bexp'_denote: forall st La b,
  beval b st <-> bexp'_denote (st, La) (binj b).
Proof.
  intros.
  induction b; simpl.
  + tauto.
  + tauto.
  + rewrite <- aeval_aexp'_denote.
    rewrite <- aeval_aexp'_denote.
    tauto.
  + rewrite <- aeval_aexp'_denote.
    rewrite <- aeval_aexp'_denote.
    tauto.
  + unfold Sets.complement.
    tauto.
  + unfold Sets.intersect.
    tauto.
Qed.

Record Interp_Equiv (J1 J2: Interp): Prop := {
  state_equiv: forall X: var, fst J1 X = fst J2 X;
  Lassn_equiv: forall x: logical_var, snd J1 x = snd J2 x
}.

Lemma Interp_Equiv_trans: forall J1 J2 J3,
  Interp_Equiv J1 J2 ->
  Interp_Equiv J2 J3 ->
  Interp_Equiv J1 J3.
Proof.
  intros.
  destruct H as [?H ?H].
  destruct H0 as [?H ?H].
  constructor.
  + intros.
    specialize (H X).
    specialize (H0 X).
    rewrite H, H0.
    reflexivity.
  + intros.
    specialize (H1 x).
    specialize (H2 x).
    rewrite H1, H2.
    reflexivity.
Qed.

Lemma Interp_Equiv_sym: forall J1 J2,
  Interp_Equiv J1 J2 ->
  Interp_Equiv J2 J1.
Proof.
  intros.
  destruct H as [?H ?H].
  constructor.
  + intros.
    rewrite H; reflexivity.
  + intros.
    rewrite H0; reflexivity.
Qed.

Lemma Interp_Equiv_Interp_Lupdate: forall J1 J2 x v,
  Interp_Equiv J1 J2 ->
  Interp_Equiv (Interp_Lupdate J1 x v) (Interp_Lupdate J2 x v).
Proof.
  intros.
  apply Build_Interp_Equiv.
  + intros.
    simpl.
    apply state_equiv.
    exact H.
  + intros.
    destruct J1 as [st1 La1], J2 as [st2 La2].
    simpl.
    unfold Lassn_update.
    destruct (Nat.eq_dec x x0).
    - reflexivity.
    - pose proof Lassn_equiv _ _ H.
      simpl in H0.
      apply H0.
Qed.

Lemma Lassn_update_update_self: forall st La x,
  Interp_Equiv
    (st, Lassn_update La x (La x))
    (st, La).
Proof.
  intros.
  apply Build_Interp_Equiv.
  + intros.
    simpl.
    reflexivity.
  + intros.
    simpl.
    unfold Lassn_update.
    destruct (Nat.eq_dec x x0).
    - subst x0;
      reflexivity.
    - reflexivity.
Qed.

Lemma Lassn_update_update_same: forall st La x v1 v2,
  Interp_Equiv
    (st, Lassn_update (Lassn_update La x v1) x v2)
    (st, Lassn_update La x v2).
Proof.
  intros.
  apply Build_Interp_Equiv.
  + intros.
    simpl.
    reflexivity.
  + intros.
    simpl.
    unfold Lassn_update.
    destruct (Nat.eq_dec x x0).
    - reflexivity.
    - reflexivity.
Qed.

Lemma Lassn_update_update_diff: forall st La x1 x2 v1 v2,
  x1 <> x2 ->
  Interp_Equiv
    (st, Lassn_update (Lassn_update La x1 v1) x2 v2)
    (st, Lassn_update (Lassn_update La x2 v2) x1 v1).
Proof.
  intros.
  apply Build_Interp_Equiv.
  + intros.
    simpl.
    reflexivity.
  + intros.
    simpl.
    unfold Lassn_update.
    destruct (Nat.eq_dec x1 x), (Nat.eq_dec x2 x).
    - exfalso.
      apply H; subst; reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
Qed.

Definition state_update (st: state) (X: var) (v: Z): state :=
  fun Y => if (Nat.eq_dec X Y) then v else st Y.

Lemma state_update_spec: forall st X v,
  (state_update st X v) X = v /\
  (forall Y, X <> Y -> st Y = (state_update st X v) Y).
Proof.
  intros.
  unfold state_update.
  split.
  + destruct (Nat.eq_dec X X).
    - reflexivity.
    - assert (X = X). { reflexivity. }
      tauto.
  + intros.
    destruct (Nat.eq_dec X Y).
    - tauto.
    - reflexivity.
Qed.

Lemma state_update_update_same: forall st La X v1 v2,
  Interp_Equiv
    (state_update (state_update st X v1) X v2, La)
    (state_update st X v2, La).
Proof.
  intros.
  apply Build_Interp_Equiv.
  + intros.
    simpl.
    unfold state_update.
    destruct (Nat.eq_dec X X0).
    - reflexivity.
    - reflexivity.
  + intros.
    simpl.
    reflexivity.
Qed.

Lemma state_update_update_diff: forall st La X1 X2 v1 v2,
  X1 <> X2 ->
  Interp_Equiv
    (state_update (state_update st X1 v1) X2 v2, La)
    (state_update (state_update st X2 v2) X1 v1, La).
Proof.
  intros.
  apply Build_Interp_Equiv.
  + intros.
    simpl.
    unfold state_update.
    destruct (Nat.eq_dec X1 X), (Nat.eq_dec X2 X).
    - exfalso.
      apply H; subst; reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
  + intros.
    simpl.
    reflexivity.
Qed.

Lemma state_update_update_self: forall st La X,
  Interp_Equiv
    (state_update st X (st X), La)
    (st, La).
Proof.
  intros.
  apply Build_Interp_Equiv.
  + intros.
    simpl.
    unfold state_update.
    destruct (Nat.eq_dec X X0).
    - subst X0;
      reflexivity.
    - reflexivity.
  + intros.
    simpl.
    reflexivity.
Qed.

Lemma aexp'_denote_Interp_Equiv: forall J1 J2 a,
  Interp_Equiv J1 J2 ->
  aexp'_denote J1 a = aexp'_denote J2 a
with term_denote_Interp_Equiv: forall J1 J2 t,
  Interp_Equiv J1 J2 ->
  term_denote J1 t = term_denote J2 t.
Proof.
{
  clear aexp'_denote_Interp_Equiv.
  intros.
  induction a; simpl.
  + apply term_denote_Interp_Equiv.
    exact H.
  + apply state_equiv.
    exact H.
  + rewrite IHa1, IHa2.
    reflexivity.
  + rewrite IHa1, IHa2.
    reflexivity.
  + rewrite IHa1, IHa2.
    reflexivity.
}
{
  clear term_denote_Interp_Equiv.
  intros.
  induction t; simpl.
  + reflexivity.
  + apply Lassn_equiv.
    exact H.
  + apply aexp'_denote_Interp_Equiv.
    exact H.
  + rewrite IHt1, IHt2.
    reflexivity.
  + rewrite IHt1, IHt2.
    reflexivity.
  + rewrite IHt1, IHt2.
    reflexivity.
}
Qed.

Lemma bexp'_denote_Interp_Equiv: forall J1 J2 b,
  Interp_Equiv J1 J2 ->
  (bexp'_denote J1 b <-> bexp'_denote J2 b).
Proof.
  intros.
  induction b; simpl.
  + tauto.
  + tauto.
  + pose proof aexp'_denote_Interp_Equiv _ _ a1 H.
    pose proof aexp'_denote_Interp_Equiv _ _ a2 H.
    rewrite H0, H1.
    tauto.
  + pose proof aexp'_denote_Interp_Equiv _ _ a1 H.
    pose proof aexp'_denote_Interp_Equiv _ _ a2 H.
    rewrite H0, H1.
    tauto.
  + tauto.
  + tauto.
Qed.

Lemma satisfies_Interp_Equiv: forall J1 J2 P,
  Interp_Equiv J1 J2 ->
  (J1 |== P <-> J2 |== P).
Proof.
  intros.
  revert J1 J2 H; induction P; simpl; intros.
  + pose proof term_denote_Interp_Equiv _ _ t1 H.
    pose proof term_denote_Interp_Equiv _ _ t2 H.
    rewrite H0, H1.
    tauto.
  + pose proof term_denote_Interp_Equiv _ _ t1 H.
    pose proof term_denote_Interp_Equiv _ _ t2 H.
    rewrite H0, H1.
    tauto.
  + pose proof term_denote_Interp_Equiv _ _ t1 H.
    pose proof term_denote_Interp_Equiv _ _ t2 H.
    rewrite H0, H1.
    tauto.
  + apply bexp'_denote_Interp_Equiv.
    exact H.
  + specialize (IHP1 _ _ H).
    specialize (IHP2 _ _ H).
    tauto.
  + specialize (IHP1 _ _ H).
    specialize (IHP2 _ _ H).
    tauto.
  + specialize (IHP1 _ _ H).
    specialize (IHP2 _ _ H).
    tauto.
  + specialize (IHP _ _ H).
    tauto.
  + apply Morphisms_Prop.ex_iff_morphism.
    hnf; intros v.
    apply IHP.
    apply Interp_Equiv_Interp_Lupdate.
    exact H.
  + apply Morphisms_Prop.all_iff_morphism.
    hnf; intros v.
    apply IHP.
    apply Interp_Equiv_Interp_Lupdate.
    exact H.
Qed.

Lemma aexp_sub_spec: forall st1 st2 La (a: aexp') (X: var) (E: aexp'),
  st2 X = aexp'_denote (st1, La) E ->
  (forall Y : var, X <> Y -> st1 Y = st2 Y) ->
  aexp'_denote (st1, La) (a [X |-> E]) = aexp'_denote (st2, La) a
with term_sub_spec: forall st1 st2 La (t: term) (X: var) (E: aexp'),
  st2 X = aexp'_denote (st1, La) E ->
  (forall Y : var, X <> Y -> st1 Y = st2 Y) ->
  term_denote (st1, La) (term_sub X E t) = term_denote (st2, La) t.
Proof.
{
  clear aexp_sub_spec.
  intros.
  induction a; simpl.
  + apply term_sub_spec; tauto.
  + destruct (Nat.eq_dec X X0); simpl.
    - subst X0.
      rewrite H.
      reflexivity.
    - apply H0.
      exact n.
  + rewrite IHa1, IHa2.
    reflexivity.
  + rewrite IHa1, IHa2.
    reflexivity.
  + rewrite IHa1, IHa2.
    reflexivity.
}
{
  clear term_sub_spec.
  intros.
  induction t; simpl.
  + reflexivity.
  + reflexivity.
  + apply aexp_sub_spec; auto.
  + rewrite IHt1, IHt2.
    reflexivity.
  + rewrite IHt1, IHt2.
    reflexivity.
  + rewrite IHt1, IHt2.
    reflexivity.
}
Qed.

Lemma bexp_sub_spec: forall st1 st2 La (b: bexp') (X: var) (E: aexp'),
  st2 X = aexp'_denote (st1, La) E ->
  (forall Y : var, X <> Y -> st1 Y = st2 Y) ->
  (bexp'_denote (st1, La) (bexp_sub X E b) <-> bexp'_denote (st2, La) b).
Proof.
  intros.
  induction b; simpl.
  + tauto.
  + tauto.
  + pose proof aexp_sub_spec _ _ _ a1 _ _ H H0.
    pose proof aexp_sub_spec _ _ _ a2 _ _ H H0.
    rewrite H1, H2.
    tauto.
  + pose proof aexp_sub_spec _ _ _ a1 _ _ H H0.
    pose proof aexp_sub_spec _ _ _ a2 _ _ H H0.
    rewrite H1, H2.
    tauto.
  + tauto.
  + tauto.
Qed.

Lemma aexp_max_var_spec: forall a x,
  (0 < aexp_occur x a)%nat ->
  (x <= aexp_max_var a)%nat
with term_max_var_spec: forall t x,
  (0 < term_occur x t)%nat ->
  (x <= term_max_var t)%nat.
Proof.
{
  clear aexp_max_var_spec.
  intros.
  induction a; simpl; simpl in H.
  + apply term_max_var_spec.
    exact H.
  + inversion H.
  + apply Nat.add_pos_cases in H.
    destruct H.
    - pose proof IHa1 H.
      eapply le_trans.
      * exact H0.
      * apply Nat.le_max_l.
    - pose proof IHa2 H.
      eapply le_trans.
      * exact H0.
      * apply Nat.le_max_r.
  + apply Nat.add_pos_cases in H.
    destruct H.
    - pose proof IHa1 H.
      eapply le_trans.
      * exact H0.
      * apply Nat.le_max_l.
    - pose proof IHa2 H.
      eapply le_trans.
      * exact H0.
      * apply Nat.le_max_r.
  + apply Nat.add_pos_cases in H.
    destruct H.
    - pose proof IHa1 H.
      eapply le_trans.
      * exact H0.
      * apply Nat.le_max_l.
    - pose proof IHa2 H.
      eapply le_trans.
      * exact H0.
      * apply Nat.le_max_r.
}
{
  clear term_max_var_spec.
  intros.
  induction t; simpl; simpl in H.
  + inversion H.
  + destruct (Nat.eq_dec x x0).
    - subst x0.
      apply le_n.
    - inversion H.
  + apply aexp_max_var_spec.
    exact H.
  + apply Nat.add_pos_cases in H.
    destruct H.
    - pose proof IHt1 H.
      eapply le_trans.
      * exact H0.
      * apply Nat.le_max_l.
    - pose proof IHt2 H.
      eapply le_trans.
      * exact H0.
      * apply Nat.le_max_r.
  + apply Nat.add_pos_cases in H.
    destruct H.
    - pose proof IHt1 H.
      eapply le_trans.
      * exact H0.
      * apply Nat.le_max_l.
    - pose proof IHt2 H.
      eapply le_trans.
      * exact H0.
      * apply Nat.le_max_r.
  + apply Nat.add_pos_cases in H.
    destruct H.
    - pose proof IHt1 H.
      eapply le_trans.
      * exact H0.
      * apply Nat.le_max_l.
    - pose proof IHt2 H.
      eapply le_trans.
      * exact H0.
      * apply Nat.le_max_r.
}
Qed.

Lemma bexp_max_var_spec: forall b x,
  (0 < bexp_occur x b)%nat ->
  (x <= bexp_max_var b)%nat.
Proof.
  intros.
  induction b; simpl; simpl in H.
  + inversion H.
  + inversion H.
  + apply Nat.add_pos_cases in H.
    destruct H.
    - pose proof aexp_max_var_spec _ _ H.
      eapply le_trans.
      * exact H0.
      * apply Nat.le_max_l.
    - pose proof aexp_max_var_spec _ _ H.
      eapply le_trans.
      * exact H0.
      * apply Nat.le_max_r.
  + apply Nat.add_pos_cases in H.
    destruct H.
    - pose proof aexp_max_var_spec _ _ H.
      eapply le_trans.
      * exact H0.
      * apply Nat.le_max_l.
    - pose proof aexp_max_var_spec _ _ H.
      eapply le_trans.
      * exact H0.
      * apply Nat.le_max_r.
  + apply IHb.
    exact H.
  + apply Nat.add_pos_cases in H.
    destruct H.
    - pose proof IHb1 H.
      eapply le_trans.
      * exact H0.
      * apply Nat.le_max_l.
    - pose proof IHb2 H.
      eapply le_trans.
      * exact H0.
      * apply Nat.le_max_r.
Qed.

Lemma assn_max_var_spec: forall P x,
  (0 < assn_occur x P)%nat ->
  (x <= assn_max_var P)%nat.
Proof.
  intros.
  induction P; simpl; simpl in H.
  + apply Nat.add_pos_cases in H.
    destruct H.
    - pose proof term_max_var_spec _ _ H.
      eapply le_trans.
      * exact H0.
      * apply Nat.le_max_l.
    - pose proof term_max_var_spec _ _ H.
      eapply le_trans.
      * exact H0.
      * apply Nat.le_max_r.
  + apply Nat.add_pos_cases in H.
    destruct H.
    - pose proof term_max_var_spec _ _ H.
      eapply le_trans.
      * exact H0.
      * apply Nat.le_max_l.
    - pose proof term_max_var_spec _ _ H.
      eapply le_trans.
      * exact H0.
      * apply Nat.le_max_r.
  + apply Nat.add_pos_cases in H.
    destruct H.
    - pose proof term_max_var_spec _ _ H.
      eapply le_trans.
      * exact H0.
      * apply Nat.le_max_l.
    - pose proof term_max_var_spec _ _ H.
      eapply le_trans.
      * exact H0.
      * apply Nat.le_max_r.
  + apply bexp_max_var_spec.
    exact H.
  + apply Nat.add_pos_cases in H.
    destruct H.
    - pose proof IHP1 H.
      eapply le_trans.
      * exact H0.
      * apply Nat.le_max_l.
    - pose proof IHP2 H.
      eapply le_trans.
      * exact H0.
      * apply Nat.le_max_r.
  + apply Nat.add_pos_cases in H.
    destruct H.
    - pose proof IHP1 H.
      eapply le_trans.
      * exact H0.
      * apply Nat.le_max_l.
    - pose proof IHP2 H.
      eapply le_trans.
      * exact H0.
      * apply Nat.le_max_r.
  + apply Nat.add_pos_cases in H.
    destruct H.
    - pose proof IHP1 H.
      eapply le_trans.
      * exact H0.
      * apply Nat.le_max_l.
    - pose proof IHP2 H.
      eapply le_trans.
      * exact H0.
      * apply Nat.le_max_r.
  + apply IHP.
    exact H.
  + destruct (Nat.eq_dec x x0).
    - subst x0.
      apply Nat.le_max_l.
    - apply IHP in H.
      eapply le_trans.
      * exact H.
      * apply Nat.le_max_r.
  + destruct (Nat.eq_dec x x0).
    - subst x0.
      apply Nat.le_max_l.
    - apply IHP in H.
      eapply le_trans.
      * exact H.
      * apply Nat.le_max_r.
Qed.

Lemma new_var_occur_r: forall E P,
  aexp_occur (new_var P E) E = O.
Proof.
  intros.
  destruct (aexp_occur (new_var P E) E) eqn:?H.
  { reflexivity. }
  assert (0 < aexp_occur (new_var P E) E)%nat as HH.
  {
    rewrite H.
    apply Nat.lt_0_succ.
  }
  exfalso.
  clear H.
  pose proof aexp_max_var_spec _ _ HH.
  unfold new_var in H.
  revert H.
  apply lt_not_le.
  apply le_lt_n_Sm.
  apply Nat.le_max_r.
Qed.

Lemma new_var_occur_l: forall E P,
  assn_occur (new_var P E) P = O.
Proof.
  intros.
  destruct (assn_occur (new_var P E) P) eqn:?H.
  { reflexivity. }
  assert (0 < assn_occur (new_var P E) P)%nat as HH.
  {
    rewrite H.
    apply Nat.lt_0_succ.
  }
  exfalso.
  clear H.
  pose proof assn_max_var_spec _ _ HH.
  unfold new_var in H.
  revert H.
  apply lt_not_le.
  apply le_lt_n_Sm.
  apply Nat.le_max_l.
Qed.

Lemma no_occ_aexp'_denote: forall st La a x v,
  aexp_occur x a = O ->
  aexp'_denote (st, La) a = aexp'_denote (st, Lassn_update La x v) a
with no_occ_term_denote: forall st La t x v,
  term_occur x t = O ->
  term_denote (st, La) t = term_denote (st, Lassn_update La x v) t.
Proof.
{
  clear no_occ_aexp'_denote.
  intros.
  induction a; simpl.
  + apply no_occ_term_denote.
    exact H.
  + reflexivity.
  + simpl in H.
    apply plus_is_O in H.
    rewrite IHa1, IHa2 by tauto.
    (** Here, [IHa1] and [IHa2] are not simple equantions. These equations only
    hold conditionally. The [rewrite ... by ...] tactic is used to handle such
    conditional equantions -- the sub-tactic after [by] is to prove those
    conditions. *)
    reflexivity.
  + simpl in H.
    apply plus_is_O in H.
    rewrite IHa1, IHa2 by tauto.
    reflexivity.
  + simpl in H.
    apply plus_is_O in H.
    rewrite IHa1, IHa2 by tauto.
    reflexivity.
}
{
  clear no_occ_term_denote.
  intros.
  induction t; simpl.
  + reflexivity.
  + simpl in H.
    unfold Lassn_update.
    destruct (Nat.eq_dec x x0).
    - discriminate H.
    - reflexivity.
  + apply no_occ_aexp'_denote.
    exact H.
  + simpl in H.
    apply plus_is_O in H.
    rewrite IHt1, IHt2 by tauto.
    reflexivity.
  + simpl in H.
    apply plus_is_O in H.
    rewrite IHt1, IHt2 by tauto.
    reflexivity.
  + simpl in H.
    apply plus_is_O in H.
    rewrite IHt1, IHt2 by tauto.
    reflexivity.
}
Qed.

Lemma no_occ_bexp'_denote: forall st La b x v,
  bexp_occur x b = O ->
  (bexp'_denote (st, La) b <-> bexp'_denote (st, Lassn_update La x v) b).
Proof.
  intros.
  induction b; simpl; simpl in H.
  + tauto.
  + tauto.
  + apply plus_is_O in H.
    pose proof no_occ_aexp'_denote st La a1 x v.
    pose proof no_occ_aexp'_denote st La a2 x v.
    rewrite H1, H0 by tauto.
    tauto.
  + apply plus_is_O in H.
    pose proof no_occ_aexp'_denote st La a1 x v.
    pose proof no_occ_aexp'_denote st La a2 x v.
    rewrite H1, H0 by tauto.
    tauto.
  + tauto.
  + apply plus_is_O in H.
    tauto.
Qed.

Lemma no_occ_satisfies: forall st La P x v,
  assn_free_occur x P = O ->
  ((st, La) |== P <-> (st, Lassn_update La x v) |== P).
Proof.
  intros.
  revert La H; induction P; simpl; intros.
  + apply plus_is_O in H.
    pose proof no_occ_term_denote st La t1 x v.
    pose proof no_occ_term_denote st La t2 x v.
    rewrite H1, H0 by tauto.
    tauto.
  + apply plus_is_O in H.
    pose proof no_occ_term_denote st La t1 x v.
    pose proof no_occ_term_denote st La t2 x v.
    rewrite H1, H0 by tauto.
    tauto.
  + apply plus_is_O in H.
    pose proof no_occ_term_denote st La t1 x v.
    pose proof no_occ_term_denote st La t2 x v.
    rewrite H1, H0 by tauto.
    tauto.
  + apply no_occ_bexp'_denote.
    exact H.
  + apply plus_is_O in H.
    specialize (IHP1 La).
    specialize (IHP2 La).
    tauto.
  + apply plus_is_O in H.
    specialize (IHP1 La).
    specialize (IHP2 La).
    tauto.
  + apply plus_is_O in H.
    specialize (IHP1 La).
    specialize (IHP2 La).
    tauto.
  + specialize (IHP La).
    tauto.
  + unfold Interp_Lupdate; simpl.
    destruct (Nat.eq_dec x x0).
    - subst x0.
      assert (forall v0, (st, Lassn_update (Lassn_update La x v) x v0) |== P <->
                         (st, Lassn_update La x v0) |== P).
      {
        intros.
        apply satisfies_Interp_Equiv.
        apply Lassn_update_update_same.
      }
      firstorder.
    - assert (forall v0, (st, Lassn_update La x0 v0) |== P <->
                         (st, Lassn_update (Lassn_update La x v) x0 v0) |== P).
      {
        intros.
        pose proof Lassn_update_update_diff st La x x0 v v0 n.
        pose proof satisfies_Interp_Equiv _ _ P H0.
        specialize (IHP (Lassn_update La x0 v0)).
        tauto.
      }
      firstorder.
  + unfold Interp_Lupdate; simpl.
    destruct (Nat.eq_dec x x0).
    - subst x0.
      assert (forall v0, (st, Lassn_update (Lassn_update La x v) x v0) |== P <->
                         (st, Lassn_update La x v0) |== P).
      {
        intros.
        apply satisfies_Interp_Equiv.
        apply Lassn_update_update_same.
      }
      firstorder.
    - assert (forall v0, (st, Lassn_update La x0 v0) |== P <->
                         (st, Lassn_update (Lassn_update La x v) x0 v0) |== P).
      {
        intros.
        pose proof Lassn_update_update_diff st La x x0 v v0 n.
        pose proof satisfies_Interp_Equiv _ _ P H0.
        specialize (IHP (Lassn_update La x0 v0)).
        tauto.
      }
      firstorder.
Qed.

Lemma no_occ_satisfies': forall st La P x v,
  assn_occur x P = O ->
  ((st, La) |== P <-> (st, Lassn_update La x v) |== P).
Proof.
  intros.
  apply no_occ_satisfies.
  apply assn_occur_O.
  exact H.
Qed.

Lemma aexp_rename_no_occur: forall st La x y v a,
  aexp_occur y a = O ->
  aexp'_denote (st, Lassn_update La x v) a =
  aexp'_denote (st, Lassn_update La y v) (aexp_rename x y a)
with term_rename_no_occur: forall st La x y v t,
  term_occur y t = O ->
  term_denote (st, Lassn_update La x v) t =
  term_denote (st, Lassn_update La y v) (term_rename x y t).
Proof.
{
  clear aexp_rename_no_occur.
  intros.
  induction a; simpl.
  + apply term_rename_no_occur.
    exact H.
  + reflexivity.
  + apply plus_is_O in H.
    rewrite IHa1, IHa2 by tauto.
    reflexivity.
  + apply plus_is_O in H.
    rewrite IHa1, IHa2 by tauto.
    reflexivity.
  + apply plus_is_O in H.
    rewrite IHa1, IHa2 by tauto.
    reflexivity.
}
{
  clear term_rename_no_occur.
  intros.
  induction t; simpl; simpl in H.
  + reflexivity.
  + destruct (Nat.eq_dec x x0).
    - subst x0.
      simpl.
      unfold Lassn_update.
      destruct (Nat.eq_dec x x); destruct (Nat.eq_dec y y).
      * reflexivity.
      * exfalso; apply n; reflexivity.
      * exfalso; apply n; reflexivity.
      * exfalso; apply n; reflexivity.
    - simpl.
      unfold Lassn_update.
      destruct (Nat.eq_dec x x0).
      { pose proof n e. destruct H0. }
      simpl in H.
      destruct (Nat.eq_dec y x0).
      { discriminate H. }
      reflexivity.
  + apply aexp_rename_no_occur.
    exact H.
  + apply plus_is_O in H.
    rewrite IHt1, IHt2 by tauto.
    reflexivity.
  + apply plus_is_O in H.
    rewrite IHt1, IHt2 by tauto.
    reflexivity.
  + apply plus_is_O in H.
    rewrite IHt1, IHt2 by tauto.
    reflexivity.
}
Qed.

Lemma bexp_rename_no_occur: forall st La x y v b,
  bexp_occur y b = O ->
  (bexp'_denote (st, Lassn_update La x v) b <->
   bexp'_denote (st, Lassn_update La y v) (bexp_rename x y b)).
Proof.
  intros.
  induction b; simpl; simpl in H.
  + tauto.
  + tauto.
  + apply plus_is_O in H.
    rewrite <- aexp_rename_no_occur by tauto.
    rewrite <- aexp_rename_no_occur by tauto.
    tauto.
  + apply plus_is_O in H.
    rewrite <- aexp_rename_no_occur by tauto.
    rewrite <- aexp_rename_no_occur by tauto.
    tauto.
  + tauto.
  + apply plus_is_O in H.
    tauto.
Qed.

Fixpoint naive_sub_safe (E: aexp') (d: Assertion): Prop :=
    match d with
    | AssnLe t1 t2   => True
    | AssnLt t1 t2   => True
    | AssnEq t1 t2   => True
    | AssnDenote b   => True
    | AssnOr P1 P2   => naive_sub_safe E P1 /\ naive_sub_safe E P2
    | AssnAnd P1 P2  => naive_sub_safe E P1 /\ naive_sub_safe E P2
    | AssnImpl P1 P2 => naive_sub_safe E P1 /\ naive_sub_safe E P2
    | AssnNot P      => naive_sub_safe E P
    | AssnExists x P => aexp_occur x E = O /\ naive_sub_safe E P
    | AssnForall x P => aexp_occur x E = O /\ naive_sub_safe E P
    end.

Lemma assn_rename_no_occur: forall st La x y v P,
  assn_occur y P = O ->
  ((st, Lassn_update La x v) |== P <->
   (st, Lassn_update La y v) |== assn_rename x y P).
Proof.
  intros.
  revert La H; induction P; intros; simpl; simpl in H.
  + apply plus_is_O in H.
    rewrite <- term_rename_no_occur by tauto.
    rewrite <- term_rename_no_occur by tauto.
    tauto.
  + apply plus_is_O in H.
    rewrite <- term_rename_no_occur by tauto.
    rewrite <- term_rename_no_occur by tauto.
    tauto.
  + apply plus_is_O in H.
    rewrite <- term_rename_no_occur by tauto.
    rewrite <- term_rename_no_occur by tauto.
    tauto.
  + apply bexp_rename_no_occur.
    exact H.
  + apply plus_is_O in H.
    specialize (IHP1 La).
    specialize (IHP2 La).
    tauto.
  + apply plus_is_O in H.
    specialize (IHP1 La).
    specialize (IHP2 La).
    tauto.
  + apply plus_is_O in H.
    specialize (IHP1 La).
    specialize (IHP2 La).
    tauto.
  + specialize (IHP La).
    tauto.
  + destruct (Nat.eq_dec x x0).
    - simpl.
      unfold Interp_Lupdate; simpl.
      destruct (Nat.eq_dec y x0).
      * subst x y.
        tauto.
      * subst x0.
        assert (forall v0 : Z,
                 (st, Lassn_update (Lassn_update La x v) x v0) |== P <->
                 (st, Lassn_update (Lassn_update La y v) x v0) |== P).
        {
          intros.
          pose proof Lassn_update_update_same st La x v v0.
          pose proof Lassn_update_update_diff st La y x v v0 n.
          pose proof satisfies_Interp_Equiv _ _ P H0.
          pose proof satisfies_Interp_Equiv _ _ P H1.
          rewrite H2, H3; clear H0 H1 H2 H3.
          apply no_occ_satisfies'.
          exact H.
        }
        clear - H0.
        firstorder.
    - simpl.
      unfold Interp_Lupdate; simpl.
      destruct (Nat.eq_dec y x0).
      * discriminate H.
      * assert (forall v0 : Z,
                 (st, Lassn_update (Lassn_update La x v) x0 v0) |== P <->
                 (st, Lassn_update (Lassn_update La y v) x0 v0) |== assn_rename x y P).
        {
          intros.
          pose proof Lassn_update_update_diff st La x x0 v v0 n.
          pose proof Lassn_update_update_diff st La y x0 v v0 n0.
          pose proof satisfies_Interp_Equiv _ _ P H0.
          pose proof satisfies_Interp_Equiv _ _ (assn_rename x y P) H1.
          rewrite H2, H3; clear H0 H1 H2 H3.
          apply IHP.
          exact H.
        }
        firstorder.
  + destruct (Nat.eq_dec x x0).
    - simpl.
      unfold Interp_Lupdate; simpl.
      destruct (Nat.eq_dec y x0).
      * subst x y.
        tauto.
      * subst x0.
        assert (forall v0 : Z,
                 (st, Lassn_update (Lassn_update La x v) x v0) |== P <->
                 (st, Lassn_update (Lassn_update La y v) x v0) |== P).
        {
          intros.
          pose proof Lassn_update_update_same st La x v v0.
          pose proof Lassn_update_update_diff st La y x v v0 n.
          pose proof satisfies_Interp_Equiv _ _ P H0.
          pose proof satisfies_Interp_Equiv _ _ P H1.
          rewrite H2, H3; clear H0 H1 H2 H3.
          apply no_occ_satisfies'.
          exact H.
        }
        clear - H0.
        firstorder.
    - simpl.
      unfold Interp_Lupdate; simpl.
      destruct (Nat.eq_dec y x0).
      * discriminate H.
      * assert (forall v0 : Z,
                 (st, Lassn_update (Lassn_update La x v) x0 v0) |== P <->
                 (st, Lassn_update (Lassn_update La y v) x0 v0) |== assn_rename x y P).
        {
          intros.
          pose proof Lassn_update_update_diff st La x x0 v v0 n.
          pose proof Lassn_update_update_diff st La y x0 v v0 n0.
          pose proof satisfies_Interp_Equiv _ _ P H0.
          pose proof satisfies_Interp_Equiv _ _ (assn_rename x y P) H1.
          rewrite H2, H3; clear H0 H1 H2 H3.
          apply IHP.
          exact H.
        }
        firstorder.
Qed.

Lemma rename_all_spec: forall st La E P,
  (st, La) |== P <->
  (st, La) |== rename_all E P.
Proof.
  intros.
  revert La; induction P; intros; simpl.
  + tauto.
  + tauto.
  + tauto.
  + tauto.
  + specialize (IHP1 La).
    specialize (IHP2 La).
    tauto.
  + specialize (IHP1 La).
    specialize (IHP2 La).
    tauto.
  + specialize (IHP1 La).
    specialize (IHP2 La).
    tauto.
  + specialize (IHP La).
    tauto.
  + assert ((exists v : Z, Interp_Lupdate (st, La) x v |== P) <->
            (exists v : Z, Interp_Lupdate (st, La) x v |== rename_all E P)).
    {
      unfold Interp_Lupdate; simpl.
      assert (forall v, (st, Lassn_update La x v) |== P <->
                        (st, Lassn_update La x v) |== rename_all E P).
      { intros. apply IHP. }
      clear - H.
      firstorder.
    }
    destruct (aexp_occur x E) eqn:?H.
    - simpl.
      exact H.
    - simpl.
      rewrite H; clear H IHP.
      remember (rename_all E P) as Q.
      clear HeqQ P.
      assert (forall v, Interp_Lupdate (st, La) x v |== Q <->
                        Interp_Lupdate (st, La) (new_var Q E) v |== assn_rename x (new_var Q E) Q).
      { intros. apply assn_rename_no_occur. apply new_var_occur_l. }
      firstorder.
  + assert ((forall v : Z, Interp_Lupdate (st, La) x v |== P) <->
            (forall v : Z, Interp_Lupdate (st, La) x v |== rename_all E P)).
    {
      unfold Interp_Lupdate; simpl.
      assert (forall v, (st, Lassn_update La x v) |== P <->
                        (st, Lassn_update La x v) |== rename_all E P).
      { intros. apply IHP. }
      clear - H.
      firstorder.
    }
    destruct (aexp_occur x E) eqn:?H.
    - simpl.
      exact H.
    - simpl.
      rewrite H; clear H IHP.
      remember (rename_all E P) as Q.
      clear HeqQ P.
      assert (forall v, Interp_Lupdate (st, La) x v |== Q <->
                        Interp_Lupdate (st, La) (new_var Q E) v |== assn_rename x (new_var Q E) Q).
      { intros. apply assn_rename_no_occur. apply new_var_occur_l. }
      firstorder.
Qed.

Lemma rename_preserves_safety: forall x y E P,
  naive_sub_safe E P ->
  aexp_occur y E = O ->
  naive_sub_safe E (assn_rename x y P).
Proof.
  intros.
  induction P; simpl in H; simpl.
  + tauto.
  + tauto.
  + tauto.
  + tauto.
  + tauto.
  + tauto.
  + tauto.
  + tauto.
  + destruct (Nat.eq_dec x x0); simpl.
    - tauto.
    - tauto.
  + destruct (Nat.eq_dec x x0); simpl.
    - tauto.
    - tauto.
Qed.

Lemma rename_all_safe: forall E P,
  naive_sub_safe E (rename_all E P).
Proof.
  intros.
  induction P; simpl.
  + tauto.
  + tauto.
  + tauto.
  + tauto.
  + tauto.
  + tauto.
  + tauto.
  + tauto.
  + destruct (aexp_occur x E) eqn:?H; simpl.
    - tauto.
    - split.
      * apply new_var_occur_r.
      * apply rename_preserves_safety.
       ++ exact IHP.
       ++ apply new_var_occur_r.
  + destruct (aexp_occur x E) eqn:?H; simpl.
    - tauto.
    - split.
      * apply new_var_occur_r.
      * apply rename_preserves_safety.
       ++ exact IHP.
       ++ apply new_var_occur_r.
Qed.

Lemma naive_sub_spec: forall st1 st2 La (P: Assertion) (X: var) (E: aexp')
  (NSS: naive_sub_safe E P),
  st2 X = aexp'_denote (st1, La) E ->
  (forall Y : var, X <> Y -> st1 Y = st2 Y) ->
  ((st1, La) |== naive_sub X E P) <-> ((st2, La) |== P).
Proof.
  intros.
  revert La H H0 NSS; induction P; simpl; intros.
  + pose proof term_sub_spec _ _ _ t1 _ _ H H0.
    pose proof term_sub_spec _ _ _ t2 _ _ H H0.
    rewrite H1, H2.
    tauto.
  + pose proof term_sub_spec _ _ _ t1 _ _ H H0.
    pose proof term_sub_spec _ _ _ t2 _ _ H H0.
    rewrite H1, H2.
    tauto.
  + pose proof term_sub_spec _ _ _ t1 _ _ H H0.
    pose proof term_sub_spec _ _ _ t2 _ _ H H0.
    rewrite H1, H2.
    tauto.
  + pose proof bexp_sub_spec _ _ _ b _ _ H H0.
    tauto.
  + specialize (IHP1 La H H0).
    specialize (IHP2 La H H0).
    tauto.
  + specialize (IHP1 La H H0).
    specialize (IHP2 La H H0).
    tauto.
  + specialize (IHP1 La H H0).
    specialize (IHP2 La H H0).
    tauto.
  + specialize (IHP La H H0).
    tauto.
  + unfold Interp_Lupdate; simpl.
    destruct NSS as [OCC NSS].
    assert (forall v, st2 X = aexp'_denote (st1, Lassn_update La x v) E).
    {
      intros.
      rewrite H.
      apply no_occ_aexp'_denote.
      exact OCC.
    }
    split; intros.
    - destruct H2 as [v ?].
      exists v.
      specialize (H1 v).
      specialize (IHP _ H1 H0 NSS).
      tauto.
    - destruct H2 as [v ?].
      exists v.
      specialize (H1 v).
      specialize (IHP _ H1 H0 NSS).
      tauto.
  + unfold Interp_Lupdate; simpl.
    destruct NSS as [OCC NSS].
    assert (forall v, st2 X = aexp'_denote (st1, Lassn_update La x v) E).
    {
      intros.
      rewrite H.
      apply no_occ_aexp'_denote.
      exact OCC.
    }
    split; intros.
    - specialize (H2 v).
      specialize (H1 v).
      specialize (IHP _ H1 H0 NSS).
      tauto.
    - specialize (H2 v).
      specialize (H1 v).
      specialize (IHP _ H1 H0 NSS).
      tauto.
Qed.

Lemma Assertion_sub_spec: forall st1 st2 La (P: Assertion) (X: var) (E: aexp'),
  st2 X = aexp'_denote (st1, La) E ->
  (forall Y : var, X <> Y -> st1 Y = st2 Y) ->
  ((st1, La) |== P[ X |-> E]) <-> ((st2, La) |== P).
Proof.
  intros.
  unfold assn_sub.
  pose proof rename_all_spec st2 La E P.
  pose proof rename_all_safe E P.
  rewrite H1; clear H1.
  remember (rename_all E P) as Q.
  clear HeqQ P.
  apply naive_sub_spec; tauto.
Qed.

End Assertion_D.

Module Admissable_Rules.

Import Assertion_D.

Definition FOL_valid (P: Assertion): Prop :=
  forall J: Interp, J |== P.

Class FOL_sound (T: FirstOrderLogic): Prop :=
  FOL_soundness: forall P: Assertion, FOL_provable P -> FOL_valid P.

Class FOL_complete (T: FirstOrderLogic): Prop :=
  FOL_completenss: forall P: Assertion, FOL_valid P -> FOL_provable P.

Section Der.

Context {T: FirstOrderLogic}
        {T_sound: FOL_sound T}
        {T_complete: FOL_complete T}.

Theorem TrivialFOL_complete_der: forall P Q,
  FOL_valid (P IMPLY Q) ->
  P |-- Q.
Proof.
  intros.
  apply T_complete, H.
Qed.

Theorem TrivialFOL_sound_der: forall P Q,
  P |-- Q ->
  FOL_valid (P IMPLY Q).
Proof.
  intros.
  apply T_sound, H.
Qed.

Theorem derives_refl: forall P, P |-- P.
Proof.
  intros.
  apply TrivialFOL_complete_der.
  unfold FOL_valid.
  intros.
  simpl.
  tauto.
Qed.

Theorem derives_trans: forall P Q R, P |-- Q -> Q |-- R -> P |-- R.
Proof.
  intros.
  apply TrivialFOL_complete_der.
  apply TrivialFOL_sound_der in H.
  apply TrivialFOL_sound_der in H0.
  unfold FOL_valid in *.
  intros.
  specialize (H J).
  specialize (H0 J).
  simpl in H, H0 |- *.
  tauto.
Qed.

Theorem AND_derives: forall P1 Q1 P2 Q2,
  P1 |-- P2 ->
  Q1 |-- Q2 ->
  P1 AND Q1 |-- P2 AND Q2.
Proof.
  intros.
  apply TrivialFOL_complete_der.
  apply TrivialFOL_sound_der in H.
  apply TrivialFOL_sound_der in H0.
  unfold FOL_valid.
  unfold FOL_valid in H.
  unfold FOL_valid in H0.
  intros.
  specialize (H J).
  specialize (H0 J).
  simpl.
  simpl in H.
  simpl in H0.
  tauto.
Qed.

Lemma hoare_consequence_pre: forall P P' c Q,
  P |-- P' ->
  |-- {{ P' }} c {{ Q }} ->
  |-- {{ P }} c {{ Q }}.
Proof.
  intros.
  eapply hoare_consequence.
  + exact H.
  + exact H0.
  + apply derives_refl.
Qed.

Lemma hoare_consequence_post: forall P c Q Q',
  |-- {{ P }} c {{ Q' }} ->
  Q' |-- Q ->
  |-- {{ P }} c {{ Q }}.
Proof.
  intros.
  eapply hoare_consequence.
  + apply derives_refl.
  + exact H.
  + exact H0.
Qed.

Lemma hoare_skip_inv: forall P Q,
  |-- {{P}} Skip {{Q}} ->
  P |-- Q.  
Proof.
  intros.
  remember ({{P}} Skip {{Q}}) as tr eqn:?H.
  revert P Q H0; induction H; intros.
  + discriminate H1.
  + injection H0 as ? ?; subst.
    apply derives_refl.
  + discriminate H1.
  + discriminate H0.
  + discriminate H0.
  + injection H2 as ? ? ?; subst.
    eapply derives_trans; [exact H |].
    eapply derives_trans; [apply IHprovable; reflexivity |].
    apply H1.
Qed.

Lemma hoare_seq_inv: forall P c1 c2 R,
  |-- {{ P }} c1 ;; c2 {{ R }} ->
  exists Q, (|-- {{ P }} c1 {{ Q }}) /\ (|-- {{ Q }} c2 {{ R }}).
Proof.
  intros.
  remember ({{P}} c1;; c2 {{R}}) as Tr.
  revert P c1 c2 R HeqTr; induction H; intros.
  + injection HeqTr as ?H ?H ?H; subst.
    exists Q.
    tauto.
  + discriminate HeqTr.
  + discriminate HeqTr.
  + discriminate HeqTr.
  + discriminate HeqTr.
  + injection HeqTr as ?H ?H ?H; subst.
    assert (({{P'}} c1;; c2 {{Q'}}) = ({{P'}} c1;; c2 {{Q'}})) by reflexivity.
    specialize (IHprovable P' c1 c2 Q' H2); clear H2.
    destruct IHprovable as [Q [? ?]].
    exists Q.
    split.
    - eapply hoare_consequence_pre.
      * exact H.
      * exact H2.
    - eapply hoare_consequence_post.
      * exact H3.
      * exact H1.
Qed.

Lemma seq_assoc_der: forall P c1 c2 c3 Q,
  |-- {{ P }} c1 ;; c2 ;; c3 {{ Q }} <->
  |-- {{ P }} (c1 ;; c2) ;; c3 {{ Q }}.
Proof.
  intros.
  split; intros.
  + apply hoare_seq_inv in H.
    destruct H as [P1 [? ?]].
    apply hoare_seq_inv in H0.
    destruct H0 as [P2 [? ?]].
    apply hoare_seq with P2.
    - apply hoare_seq with P1.
      * exact H.
      * exact H0.
    - exact H1.
  + apply hoare_seq_inv in H.
    destruct H as [P2 [? ?]].
    apply hoare_seq_inv in H.
    destruct H as [P1 [? ?]].
    apply hoare_seq with P1.
    - exact H.
    - apply hoare_seq with P2.
      * exact H1.
      * exact H0.
Qed.

Lemma hoare_if_inv: forall P b c1 c2 Q,
  |-- {{P}} If b Then c1 Else c2 EndIf {{Q}} ->
  (|-- {{ P  AND {[b]} }} c1 {{Q}}) /\
  (|-- {{ P  AND NOT {[b]} }} c2 {{Q}}).
Proof.
  intros.
  remember ({{P}} If b Then c1 Else c2 EndIf {{Q}}) as Tr.
  revert P b c1 c2 Q HeqTr; induction H; intros.
  + discriminate HeqTr.
  + discriminate HeqTr.
  + injection HeqTr as ? ? ? ? ?; subst.
    clear IHprovable1 IHprovable2.
    tauto.
  + discriminate HeqTr.
  + discriminate HeqTr.
  + injection HeqTr as ? ? ?; subst.
    assert ({{P'}} If b Then c1 Else c2 EndIf {{Q'}} = 
            {{P'}} If b Then c1 Else c2 EndIf {{Q'}}).
    { reflexivity. }
    pose proof IHprovable _ _ _ _ _ H2; clear IHprovable H2.
    destruct H3.
    split.
    - eapply hoare_consequence.
      * apply AND_derives.
        { exact H. }
        { apply derives_refl. }
      * apply H2.
      * apply H1.
    - eapply hoare_consequence.
      * apply AND_derives.
        { exact H. }
        { apply derives_refl. }
      * apply H3.
      * apply H1.
Qed.

Lemma if_seq_der : forall P b c1 c2 c3 Q,
  |-- {{ P }} If b Then c1 Else c2 EndIf;; c3 {{ Q }} ->
  |-- {{ P }} If b Then c1;; c3 Else c2;; c3 EndIf {{ Q }}.
Proof.
  intros.
  apply hoare_seq_inv in H.
  destruct H as [Q' [? ?]].
  apply hoare_if_inv in H.
  destruct H.
  apply hoare_if.
  + apply hoare_seq with Q'.
    - exact H.
    - exact H0.
  + apply hoare_seq with Q'.
    - exact H1.
    - exact H0.
Qed.

Lemma seq_skip: forall c P Q,
  |-- {{ P }} c;; Skip {{ Q }} <-> |-- {{ P }} c {{ Q }}.
Proof.
  intros; split; intros.
  + apply hoare_seq_inv in H.
    destruct H as [R [? ?]].
    apply hoare_skip_inv in H0.
    apply hoare_consequence_post with R; tauto.
  + apply hoare_seq with Q.
    - exact H.
    - apply hoare_skip.
Qed.

Lemma Hoare_triple_congr_CSeq: forall c1 c1' c2 c2',
  (forall P Q, |-- {{ P }} c1 {{ Q}} <-> |-- {{ P }} c1' {{ Q }}) ->
  (forall P Q, |-- {{ P }} c2 {{ Q}} <-> |-- {{ P }} c2' {{ Q }}) ->
  (forall P Q, |-- {{ P }} c1;; c2 {{ Q}} <-> |-- {{ P }} c1';; c2' {{ Q }}).
Proof.
  intros.
  split; intros; apply hoare_seq_inv in H1; destruct H1 as [? [? ?]];
  (eapply hoare_seq; [apply H, H1 | apply H0, H2]).
Qed.

End Der.

End Admissable_Rules.

(*******************************************)
(***** Denotations vs Small Step ***********)
(*******************************************)

Section DenotationSmallStep.

Local Open Scope imp.

Theorem multi_congr_APlus1: forall st a1 a1' a2,
  multi_astep st a1 a1' ->
  multi_astep st (a1 + a2) (a1' + a2).
Proof.
  intros.
  induction_n1 H.
  + reflexivity.
  + etransitivity_n1.
    - apply IHrt.
    - apply AS_Plus1.
      exact H.
Qed.

Theorem multi_congr_APlus2: forall st a1 a2 a2',
  aexp_halt a1 ->
  multi_astep st a2 a2' ->
  multi_astep st (a1 + a2) (a1 + a2').

Proof.
  intros.
  induction_n1 H0.
  + reflexivity.
  + etransitivity_n1.
    - apply IHrt.
    - apply AS_Plus2.
      * exact H.
      * exact H0.
Qed.

Theorem multi_congr_AMinus1: forall st a1 a1' a2,
  multi_astep st a1 a1' ->
  multi_astep st (a1 - a2) (a1' - a2).

Proof.
  intros.
  induction_n1 H.
  + reflexivity.
  + etransitivity_n1.
    - apply IHrt.
    - apply AS_Minus1.
      exact H.
Qed.

Theorem multi_congr_AMinus2: forall st a1 a2 a2',
  aexp_halt a1 ->
  multi_astep st a2 a2' ->
  multi_astep st (a1 - a2) (a1 - a2').

Proof.
  intros.
  induction_n1 H0.
  + reflexivity.
  + etransitivity_n1.
    - apply IHrt.
    - apply AS_Minus2.
      * exact H.
      * exact H0.
Qed.

Theorem multi_congr_AMult1: forall st a1 a1' a2,
  multi_astep st a1 a1' ->
  multi_astep st (a1 * a2) (a1' * a2).

Proof.
  intros.
  induction_n1 H.
  + reflexivity.
  + etransitivity_n1.
    - apply IHrt.
    - apply AS_Mult1.
      exact H.
Qed.

Theorem multi_congr_AMult2: forall st a1 a2 a2',
  aexp_halt a1 ->
  multi_astep st a2 a2' ->
  multi_astep st (a1 * a2) (a1 * a2').

Proof.
  intros.
  induction_n1 H0.
  + reflexivity.
  + etransitivity_n1.
    - apply IHrt.
    - apply AS_Mult2.
      * exact H.
      * exact H0.
Qed.

Theorem multi_congr_BEq1: forall st a1 a1' a2,
  multi_astep st a1 a1' ->
  multi_bstep st (a1 == a2) (a1' == a2).

Proof.
  intros.
  induction_n1 H.
  + reflexivity.
  + etransitivity_n1.
    - exact IHrt.
    - apply BS_Eq1.
      exact H.
Qed.

Theorem multi_congr_BEq2: forall st a1 a2 a2',
  aexp_halt a1 ->
  multi_astep st a2 a2' ->
  multi_bstep st (a1 == a2) (a1 == a2').

Proof.
  intros.
  induction_n1 H0.
  + reflexivity.
  + etransitivity_n1.
    - exact IHrt.
    - apply BS_Eq2.
      * exact H.
      * exact H0.
Qed.

Theorem multi_congr_BLe1: forall st a1 a1' a2,
  multi_astep st a1 a1' ->
  multi_bstep st (a1 <= a2) (a1' <= a2).

Proof.
  intros.
  induction_n1 H.
  + reflexivity.
  + etransitivity_n1.
    - exact IHrt.
    - apply BS_Le1.
      exact H.
Qed.

Theorem multi_congr_BLe2: forall st a1 a2 a2',
  aexp_halt a1 ->
  multi_astep st a2 a2' ->
  multi_bstep st (a1 <= a2) (a1 <= a2').

Proof.
  intros.
  induction_n1 H0.
  + reflexivity.
  + etransitivity_n1.
    - exact IHrt.
    - apply BS_Le2.
      * exact H.
      * exact H0.
Qed.

Theorem multi_congr_BNot: forall st b b',
  multi_bstep st b b' ->
  multi_bstep st (BNot b) (BNot b').

Proof.
  intros.
  induction_n1 H.
  + reflexivity.
  + etransitivity_n1.
    - apply IHrt.
    - apply BS_NotStep.
      exact H.
Qed.

Theorem multi_congr_BAnd: forall st b1 b1' b2,
  multi_bstep st b1 b1' ->
  multi_bstep st (BAnd b1 b2) (BAnd b1' b2).

Proof.
  intros.
  induction_n1 H.
  + reflexivity.
  + etransitivity_n1.
    - apply IHrt.
    - apply BS_AndStep.
      exact H.
Qed.

Theorem multi_congr_CAss: forall st X a a',
  multi_astep st a a' ->
  multi_cstep (CAss X a, st) (CAss X a', st).

Proof.
  intros.
  induction_n1 H.
  + reflexivity.
  + etransitivity_n1.
    - exact IHrt.
    - apply CS_AssStep.
      exact H.
Qed.

Theorem multi_congr_CSeq: forall st1 c1 st1' c1' c2,
  multi_cstep (c1, st1) (c1', st1') ->
  multi_cstep (CSeq c1 c2, st1) (CSeq c1' c2, st1').

Proof.
  intros.
  induction_n1 H.
  + reflexivity.
  + etransitivity_n1.
    - exact IHrt.
    - apply CS_SeqStep.
      exact H.
Qed.

Theorem multi_congr_CIf: forall st b b' c1 c2,
  multi_bstep st b b' ->
  multi_cstep
    (CIf b c1 c2, st)
    (CIf b' c1 c2, st).

Proof.
  intros.
  induction_n1 H.
  + reflexivity.
  + etransitivity_n1.
    - exact IHrt.
    - apply CS_IfStep.
      exact H.
Qed.

(* ################################################################# *)
(** * From Denotations To Multi-step Relations *)

Theorem semantic_equiv_aexp1: forall st a n,
  aeval a st = n -> multi_astep st a (ANum n).
Proof.
  intros.
  revert n H; induction a; intros; simpl in H.
  + unfold constant_func in H.
    rewrite H.
    reflexivity.
  + rewrite <- H.
    etransitivity_n1; [reflexivity |].
    apply AS_Id.
  + etransitivity.
    { apply multi_congr_APlus1, IHa1. reflexivity. }
    etransitivity_n1.
    { apply multi_congr_APlus2; [apply AH_num |]. apply IHa2. reflexivity. }
    rewrite <- H.
    apply AS_Plus.
  + etransitivity.
    { apply multi_congr_AMinus1, IHa1. reflexivity. }
    etransitivity_n1.
    { apply multi_congr_AMinus2; [apply AH_num |]. apply IHa2. reflexivity. }
    rewrite <- H.
    apply AS_Minus.
  + etransitivity.
    { apply multi_congr_AMult1, IHa1. reflexivity. }
    etransitivity_n1.
    { apply multi_congr_AMult2; [apply AH_num |]. apply IHa2. reflexivity. }
    rewrite <- H.
    apply AS_Mult.
Qed.

Theorem semantic_equiv_bexp1: forall st b,
  (beval b st -> multi_bstep st b BTrue) /\
  (~ beval b st -> multi_bstep st b BFalse).
Proof.
  intros.
  induction b; simpl.
  + split.
    - intros.
      reflexivity.
    - unfold Sets.full.
      tauto.
  + split.
    - unfold Sets.empty.
      tauto.
    - intros.
      reflexivity.
  + assert (multi_bstep st (a1 == a2) (aeval a1 st == aeval a2 st)).
    {
      etransitivity.
      - apply multi_congr_BEq1, semantic_equiv_aexp1.
        reflexivity.
      - apply multi_congr_BEq2; [apply AH_num |].
        apply semantic_equiv_aexp1.
        reflexivity.
    }
    split; unfold Func.test_eq; intros;
    (etransitivity_n1; [exact H |]).
    - apply BS_Eq_True, H0.
    - apply BS_Eq_False, H0.
  + assert (multi_bstep st (a1 <= a2) (aeval a1 st <= aeval a2 st)).
    {
      etransitivity.
      - apply multi_congr_BLe1, semantic_equiv_aexp1.
        reflexivity.
      - apply multi_congr_BLe2; [apply AH_num |].
        apply semantic_equiv_aexp1.
        reflexivity.
    }
    split; unfold Func.test_le; intros;
    (etransitivity_n1; [exact H |]).
    - apply BS_Le_True, H0.
    - apply BS_Le_False.
      lia.
  + destruct IHb as [IH1 IH2].
    split; intros.
    - etransitivity_n1.
      * apply multi_congr_BNot, IH2.
        unfold Sets.complement in H; exact H.
      * apply BS_NotFalse.
    - etransitivity_n1.
      * apply multi_congr_BNot, IH1.
        unfold Sets.complement in H; tauto.
      * apply BS_NotTrue.
  + destruct IHb1 as [IHb11 IHb12].
    destruct IHb2 as [IHb21 IHb22].
    pose proof classic (beval b1 st).
    destruct H.
    - assert (multi_bstep st (b1 && b2) b2).
      {
        etransitivity_n1.
        * apply multi_congr_BAnd, IHb11, H.
        * apply BS_AndTrue.
      }
      split; unfold Sets.intersect; intros;
      (etransitivity; [exact H0 |]).
      * apply IHb21; tauto.
      * apply IHb22; tauto.
    - split; unfold Sets.intersect; intros; [ tauto |].
      etransitivity_n1.
      * apply multi_congr_BAnd, IHb12, H.
      * apply BS_AndFalse.
Qed.

Corollary semantic_equiv_bexp1_true: forall st b,
  beval b st -> multi_bstep st b BTrue.
Proof. intros. pose proof semantic_equiv_bexp1 st b. tauto. Qed.
  
Corollary semantic_equiv_bexp1_false: forall st b,
  (Sets.complement (beval b) st -> multi_bstep st b BFalse).
Proof. intros. pose proof semantic_equiv_bexp1 st b. tauto. Qed.

Lemma semantic_equiv_iter_loop1: forall st1 st2 n b c,
  (forall st1 st2, ceval c st1 st2 -> multi_cstep (c, st1) (Skip, st2)) ->
  iter_loop_body b (ceval c) n st1 st2 ->
  multi_cstep (While b Do c EndWhile, st1) (Skip, st2).
Proof.
  intros.
  revert st1 st2 H0; induction n; intros.
  + simpl in H0.
    unfold BinRel.test_rel in H0.
    destruct H0.
    subst st2.
    etransitivity_1n; [apply CS_While |].
    etransitivity; [apply multi_congr_CIf, semantic_equiv_bexp1_false, H1 |].
    etransitivity_1n; [apply CS_IfFalse |].
    reflexivity.
  + simpl in H0.
    unfold BinRel.concat at 1,
           BinRel.test_rel in H0.
    destruct H0 as [st [[? H0] ?]]; subst st.
    unfold BinRel.concat in H2.
    destruct H2 as [st1' [? ?]].
    etransitivity_1n; [apply CS_While |].
    etransitivity; [apply multi_congr_CIf, semantic_equiv_bexp1_true, H0 |].
    etransitivity_1n; [apply CS_IfTrue |].
    etransitivity; [apply multi_congr_CSeq, H, H1 |].
    etransitivity_1n; [apply CS_Seq |].
    apply IHn, H2.
Qed.

Theorem semantic_equiv_com1: forall st1 st2 c,
  ceval c st1 st2 -> multi_cstep (c, st1) (Skip, st2).
Proof.
  intros.
  revert st1 st2 H; induction c; intros.
  + rewrite ceval_CSkip in H.
    unfold BinRel.id in H.
    rewrite H.
    reflexivity.
  + rewrite ceval_CAss in H.
    destruct H.
    etransitivity_n1.
    - apply multi_congr_CAss, semantic_equiv_aexp1.
      reflexivity.
    - apply CS_Ass; tauto.
  + rewrite ceval_CSeq in H.
    unfold BinRel.concat in H.
    destruct H as [st' [? ?]].
    etransitivity; [apply multi_congr_CSeq, IHc1, H |].
    etransitivity_1n; [ apply CS_Seq |].
    apply IHc2, H0.
  + rewrite ceval_CIf in H.
    unfold if_sem in H.
    unfold BinRel.union,
           BinRel.concat,
           BinRel.test_rel in H.
    pose proof semantic_equiv_bexp1 st1 b.
    destruct H0.
    destruct H as [H | H]; destruct H as [st [[? ?] ?]]; subst st.
    - etransitivity; [apply multi_congr_CIf, H0, H2 |].
      etransitivity_1n; [apply CS_IfTrue |].
      apply IHc1, H3.
    - etransitivity; [apply multi_congr_CIf, H1, H2 |].
      etransitivity_1n; [apply CS_IfFalse |].
      apply IHc2, H3.
  + rewrite ceval_CWhile in H.
    unfold loop_sem in H.
    unfold BinRel.omega_union in H.
    destruct H as [n ?].
    apply semantic_equiv_iter_loop1 with n.
    - exact IHc.
    - exact H.
Qed.

(* ################################################################# *)
(** * Properties Of Execution Paths *)

Local Open Scope Z.
Local Close Scope imp.

Lemma ANum_halt: forall st n a,
  multi_astep st (ANum n) a ->
  a = ANum n.

Proof.
  unfold_with_1n multi_astep.
  intros.
  inversion H; subst.
  + reflexivity.
  + inversion H0.
Qed.

Lemma never_BFalse_to_BTrue: forall st,
  multi_bstep st BFalse BTrue -> False.

Proof.
  unfold_with_1n multi_bstep.
  intros.
  inversion H; subst.
  inversion H0.
Qed.

Lemma never_BTrue_to_BFalse: forall st,
  multi_bstep st BTrue BFalse -> False.

Proof.
  unfold_with_1n multi_bstep.
  intros.
  inversion H; subst.
  inversion H0.
Qed.

Lemma CSkip_halt: forall st st' c,
  multi_cstep (CSkip, st) (c, st') ->
  c = CSkip /\ st = st'.
Proof.

  unfold_with_1n multi_cstep.
  intros.
  inversion H; subst.
  + split; reflexivity.
  + inversion H0.
Qed.

Lemma APlus_path_spec: forall st a1 a2 n,
  multi_astep st (APlus a1 a2) (ANum n) ->
  exists n1 n2,
  multi_astep st a1 (ANum n1) /\
  multi_astep st a2 (ANum n2) /\
  n = (n1 + n2).
Proof.
  intros.
  remember (APlus a1 a2) as a eqn:H0.
  remember (ANum n) as a' eqn:H1.
  revert a1 a2 n H0 H1; induction_1n H; intros; subst.
  + discriminate H1.
  + inversion H; subst.
    - specialize (IHrt _ _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      assert (multi_astep st a1 n1). { etransitivity_1n; eassumption. }
      tauto.
    - specialize (IHrt _ _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      assert (multi_astep st a2 n2). { etransitivity_1n; eassumption. }
      tauto.
    - clear IHrt.
      apply ANum_halt in H0.
      injection H0 as H1.
      exists n1, n2.
      split; [reflexivity | split; [reflexivity | tauto]].
Qed.

Lemma AMinus_path_spec: forall st a1 a2 n,
  multi_astep st (AMinus a1 a2) (ANum n) ->
  exists n1 n2,
  multi_astep st a1 (ANum n1) /\
  multi_astep st a2 (ANum n2) /\
  n = (n1 - n2).
Proof.
  intros.
  remember (AMinus a1 a2) as a eqn:H0.
  remember (ANum n) as a' eqn:H1.
  revert a1 a2 n H0 H1; induction_1n H; intros; subst.
  + discriminate H1.
  + inversion H; subst.
    - specialize (IHrt _ _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      assert (multi_astep st a1 n1). { etransitivity_1n; eassumption. }
      tauto.
    - specialize (IHrt _ _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      assert (multi_astep st a2 n2). { etransitivity_1n; eassumption. }
      tauto.
    - clear IHrt.
      apply ANum_halt in H0.
      injection H0 as H1.
      exists n1, n2.
      split; [reflexivity | split; [reflexivity | tauto]].
Qed.

Lemma AMult_path_spec: forall st a1 a2 n,
  multi_astep st (AMult a1 a2) (ANum n) ->
  exists n1 n2,
  multi_astep st a1 (ANum n1) /\
  multi_astep st a2 (ANum n2) /\
  n = (n1 * n2).
Proof.
  intros.
  remember (AMult a1 a2) as a eqn:H0.
  remember (ANum n) as a' eqn:H1.
  revert a1 a2 n H0 H1; induction_1n H; intros; subst.
  + discriminate H1.
  + inversion H; subst.
    - specialize (IHrt _ _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      assert (multi_astep st a1 n1). { etransitivity_1n; eassumption. }
      tauto.
    - specialize (IHrt _ _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      assert (multi_astep st a2 n2). { etransitivity_1n; eassumption. }
      tauto.
    - clear IHrt.
      apply ANum_halt in H0.
      injection H0 as H1.
      exists n1, n2.
      split; [reflexivity | split; [reflexivity | tauto]].
Qed.

Lemma BEq_True_path_spec: forall st a1 a2,
  multi_bstep st (BEq a1 a2) BTrue ->
  exists n1 n2,
  multi_astep st a1 (ANum n1) /\
  multi_astep st a2 (ANum n2) /\
  n1 = n2.
Proof.
  intros.
  remember (BEq a1 a2) as a eqn:H0.
  remember BTrue as a' eqn:H1.
  revert a1 a2 H0 H1; induction_1n H; intros; subst.
  + discriminate H1.
  + inversion H; subst.
    - specialize (IHrt _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      assert (multi_astep st a1 n1). { etransitivity_1n; eassumption. }
      tauto.
    - specialize (IHrt _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      assert (multi_astep st a2 n2). { etransitivity_1n; eassumption. }
      tauto.
    - clear IHrt.
      exists n2, n2.
      assert (multi_astep st n2 n2). { reflexivity. }
      tauto.
    - apply never_BFalse_to_BTrue in H0.
      destruct H0.
Qed.

Lemma BEq_False_path_spec: forall st a1 a2,
  multi_bstep st (BEq a1 a2) BFalse ->
  exists n1 n2,
  multi_astep st a1 (ANum n1) /\
  multi_astep st a2 (ANum n2) /\
  n1 <> n2.
Proof.
  intros.
  remember (BEq a1 a2) as a eqn:H0.
  remember BFalse as a' eqn:H1.
  revert a1 a2 H0 H1; induction_1n H; intros; subst.
  + discriminate H1.
  + inversion H; subst.
    - specialize (IHrt _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      assert (multi_astep st a1 n1). { etransitivity_1n; eassumption. }
      tauto.
    - specialize (IHrt _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      assert (multi_astep st a2 n2). { etransitivity_1n; eassumption. }
      tauto.
    - apply never_BTrue_to_BFalse in H0.
      destruct H0.
    - clear IHrt.
      exists n1, n2.
      assert (multi_astep st n1 n1). { reflexivity. }
      assert (multi_astep st n2 n2). { reflexivity. }
      tauto.
Qed.

Lemma BLe_True_path_spec: forall st a1 a2,
  multi_bstep st (BLe a1 a2) BTrue ->
  exists n1 n2,
  multi_astep st a1 (ANum n1) /\
  multi_astep st a2 (ANum n2) /\
  n1 <= n2.
Proof.
  intros.
  remember (BLe a1 a2) as a eqn:H0.
  remember BTrue as a' eqn:H1.
  revert a1 a2 H0 H1; induction_1n H; intros; subst.
  + discriminate H1.
  + inversion H; subst.
    - specialize (IHrt _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      assert (multi_astep st a1 n1). { etransitivity_1n; eassumption. }
      tauto.
    - specialize (IHrt _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      assert (multi_astep st a2 n2). { etransitivity_1n; eassumption. }
      tauto.
    - clear IHrt.
      exists n1, n2.
      assert (multi_astep st n1 n1). { reflexivity. }
      assert (multi_astep st n2 n2). { reflexivity. }
      tauto.
    - apply never_BFalse_to_BTrue in H0.
      destruct H0.
Qed.

Lemma BLe_False_path_spec: forall st a1 a2,
  multi_bstep st (BLe a1 a2) BFalse ->
  exists n1 n2,
  multi_astep st a1 (ANum n1) /\
  multi_astep st a2 (ANum n2) /\
  n1 > n2.
Proof.
  intros.
  remember (BLe a1 a2) as a eqn:H0.
  remember BFalse as a' eqn:H1.
  revert a1 a2 H0 H1; induction_1n H; intros; subst.
  + discriminate H1.
  + inversion H; subst.
    - specialize (IHrt _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      assert (multi_astep st a1 n1). { etransitivity_1n; eassumption. }
      tauto.
    - specialize (IHrt _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      assert (multi_astep st a2 n2). { etransitivity_1n; eassumption. }
      tauto.
    - apply never_BTrue_to_BFalse in H0.
      destruct H0.
    - clear IHrt.
      exists n1, n2.
      assert (multi_astep st n1 n1). { reflexivity. }
      assert (multi_astep st n2 n2). { reflexivity. }
      tauto.
Qed.

Lemma BNot_True_path_spec: forall st b,
  multi_bstep st (BNot b) BTrue ->
  multi_bstep st b BFalse.
Proof.
  intros.
  remember (BNot b) as b1 eqn:H0.
  remember BTrue as b2 eqn:H1.
  revert b H0 H1; induction_1n H; intros; subst.
  + discriminate H1.
  + inversion H; subst.
    - specialize (IHrt _ ltac:(reflexivity) ltac:(reflexivity)).
      etransitivity_1n; eassumption.
    - apply never_BFalse_to_BTrue in H0.
      destruct H0.
    - reflexivity.
Qed.

Lemma BNot_False_path_spec: forall st b,
  multi_bstep st (BNot b) BFalse ->
  multi_bstep st b BTrue.
Proof.
  intros.
  remember (BNot b) as b1 eqn:H0.
  remember BFalse as b2 eqn:H1.
  revert b H0 H1; induction_1n H; intros; subst.
  + discriminate H1.
  + inversion H; subst.
    - specialize (IHrt _ ltac:(reflexivity) ltac:(reflexivity)).
      etransitivity_1n; eassumption.
    - reflexivity.
    - apply never_BTrue_to_BFalse in H0.
      destruct H0.
Qed.

Lemma BAnd_True_path_spec: forall st b1 b2,
  multi_bstep st (BAnd b1 b2) BTrue ->
  multi_bstep st b1 BTrue /\
  multi_bstep st b2 BTrue.
Proof.
  intros.
  remember (BAnd b1 b2) as b eqn:H0.
  remember BTrue as b' eqn:H1.
  revert b1 b2 H0 H1; induction_1n H; intros; subst.
  + discriminate H1.
  + inversion H; subst.
    - specialize (IHrt _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt.
      assert (multi_bstep st b1 BTrue). { etransitivity_1n; eassumption. }
      tauto.
    - split.
      * reflexivity.
      * exact H0.
    - apply never_BFalse_to_BTrue in H0.
      destruct H0.
Qed.

Lemma BAnd_False_path_spec: forall st b1 b2,
  multi_bstep st (BAnd b1 b2) BFalse ->
  multi_bstep st b1 BFalse \/
  multi_bstep st b2 BFalse.
Proof.
  intros.
  remember (BAnd b1 b2) as b eqn:H0.
  remember BFalse as b' eqn:H1.
  revert b1 b2 H0 H1; induction_1n H; intros; subst.
  + discriminate H1.
  + inversion H; subst.
    - specialize (IHrt _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt.
      * assert (multi_bstep st b1 BFalse). { etransitivity_1n; eassumption. }
        tauto.
      * tauto.
    - right.
      exact H0.
    - left.
      reflexivity.
Qed.

Lemma CAss_path_spec: forall X a st1 st2,
  multi_cstep (CAss X a, st1) (CSkip, st2) ->
  exists n,
  multi_astep st1 a (ANum n) /\
  st2 X = n /\
  (forall Y : var, X <> Y -> st1 Y = st2 Y).
Proof.
  intros.
  remember (CAss X a) as c eqn:H0.
  remember CSkip as c' eqn:H1.
  revert a H0 H1; induction_1n H; intros; subst.
  + inversion H1.
  + inversion H; subst.
    - specialize (IHrt _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt as [n [? ?]].
      exists n.
      assert (multi_astep s a n). { etransitivity_1n; eassumption. }
      tauto.
    - clear IHrt.
      apply CSkip_halt in H0.
      destruct H0.
      subst s.
      exists (st2 X).
      split; [reflexivity | tauto].
Qed.

Lemma CSeq_path_spec: forall c1 st1 c2 st3,
  multi_cstep (CSeq c1 c2, st1) (CSkip, st3) ->
  exists st2,
  multi_cstep (c1, st1) (CSkip, st2) /\
  multi_cstep (c2, st2) (CSkip, st3).
Proof.
  intros.
  remember (CSeq c1 c2) as c eqn:H0.
  remember CSkip as c' eqn:H1.
  revert c1 c2 H0 H1; induction_1n H; intros; subst.
  + inversion H1.
  + inversion H; subst.
    - specialize (IHrt _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt as [st2 [? ?]].
      exists st2.
      assert (multi_cstep (c1, st1) (Skip%imp, st2)).
      { etransitivity_1n; eassumption. }
      tauto.
    - exists s.
      split; [reflexivity | tauto].
Qed.

Lemma CIf_path_spec: forall b c1 c2 st1 st2,
  multi_cstep (CIf b c1 c2, st1) (CSkip, st2) ->
  multi_bstep st1 b BTrue /\
  multi_cstep (c1, st1) (CSkip, st2) \/
  multi_bstep st1 b BFalse /\
  multi_cstep (c2, st1) (CSkip, st2).
Proof.
  intros.
  remember (CIf b c1 c2) as c eqn:H0.
  remember CSkip as c' eqn:H1.
  revert b c1 c2 H0 H1; induction_1n H; intros; subst.
  + inversion H1.
  + inversion H; subst.
    - specialize (IHrt _ _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt as [[? ?] | [? ?]].
      * assert (multi_bstep s b BTrue). { etransitivity_1n; eassumption. }
        tauto.
      * assert (multi_bstep s b BFalse). { etransitivity_1n; eassumption. }
        tauto.
    - assert (multi_bstep s BTrue BTrue). { reflexivity. }
      tauto.
    - assert (multi_bstep s BFalse BFalse). { reflexivity. }
      tauto.
Qed.

Fixpoint CWhile_path b c1 st1 st2 (n: nat): Prop:=
  match n with
  | O => multi_bstep st1 b BFalse /\ st1 = st2
  | S n' => exists st1',
            multi_bstep st1 b BTrue /\
            multi_cstep (c1, st1) (CSkip, st1') /\
            CWhile_path b c1 st1' st2 n'
  end.

Definition CWhile_path' b' b c1 st1 st2 (n: nat): Prop:=
  match n with
  | O => multi_bstep st1 b' BFalse /\ st1 = st2
  | S n' => exists st1',
            multi_bstep st1 b' BTrue /\
            multi_cstep (c1, st1) (CSkip, st1') /\
            CWhile_path b c1 st1' st2 n'
  end.

Definition CWhile_path'' c1' b c1 st1 st2 (n: nat): Prop:=
  exists st1',
    multi_cstep (c1', st1) (CSkip, st1') /\
    CWhile_path b c1 st1' st2 n.

Lemma CWhile_path_spec_aux: forall st1 st2 c c',
  multi_cstep (c, st1) (c', st2) ->
  (forall b c1,
     c = CWhile b c1 ->
     c' = Skip%imp ->
     exists n, CWhile_path b c1 st1 st2 n) /\
  (forall b' b c1,
     c = CIf b' (CSeq c1 (CWhile b c1)) CSkip ->
     c' = Skip%imp ->
     exists n, CWhile_path' b' b c1 st1 st2 n) /\
  (forall c1' b c1,
     c = CSeq c1' (CWhile b c1) ->
     c' = Skip%imp ->
     exists n, CWhile_path'' c1' b c1 st1 st2 n).
Proof.
  intros.
  induction_1n H; intros.
  + split.
    { intros; subst. inversion H0. }
    split.
    { intros; subst. inversion H0. }
    { intros; subst. inversion H0. }
  + split; [| split].
    - intros; subst.
      destruct IHrt as [_ [IHrt _]].
      inversion H; subst.
      specialize (IHrt _ _ _  ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt as [n ?].
      exists n.
      destruct n; exact H1.
    - intros; subst.
      inversion H; subst.
      * destruct IHrt as [_ [IHrt _]].
        specialize (IHrt _ _ _  ltac:(reflexivity) ltac:(reflexivity)).
        destruct IHrt as [n ?].
        exists n.
        destruct n; simpl in H1; simpl.
       ++ destruct H1.
          split; [etransitivity_1n; eassumption | tauto].
       ++ destruct H1 as [st1' [? [? ?]]].
          exists st1'.
          split; [etransitivity_1n; eassumption | tauto].
      * destruct IHrt as [_ [_ IHrt]].
        specialize (IHrt _ _ _  ltac:(reflexivity) ltac:(reflexivity)).
        destruct IHrt as [n ?].
        exists (S n).
        unfold CWhile_path'' in H1.
        simpl.
        destruct H1 as [st1' [? ?]].
        exists st1'.
        assert (multi_bstep s BTrue BTrue). { reflexivity. }
        tauto.
      * exists O.
        simpl.
        assert (multi_bstep s BFalse BFalse). { reflexivity. }
        apply CSkip_halt in H0.
        tauto.
    - intros; subst.
      inversion H; subst.
      * destruct IHrt as [_ [_ IHrt]].
        specialize (IHrt _ _ _  ltac:(reflexivity) ltac:(reflexivity)).
        destruct IHrt as [n ?].
        exists n.
        unfold CWhile_path'' in H1.
        unfold CWhile_path''.
        destruct H1 as [st1' [? ?]].
        exists st1'.
        assert (multi_cstep (c1', st1) (Skip%imp, st1')).
        { etransitivity_1n; eassumption. }
        tauto.
      * destruct IHrt as [IHrt [? ?]].
        specialize (IHrt _ _ ltac:(reflexivity) ltac:(reflexivity)).
        destruct IHrt as [n ?].
        exists n.
        unfold CWhile_path''.
        exists s.
        split; [reflexivity | tauto].
Qed.

Lemma CWhile_path_spec: forall b c1 st1 st2,
  multi_cstep (CWhile b c1, st1) (CSkip, st2) ->
  exists n, CWhile_path b c1 st1 st2 n.
Proof.
  intros.
  remember (CWhile b c1) as c eqn:H0.
  remember CSkip as c' eqn:H1.
  revert b c1 H0 H1.
  pose proof CWhile_path_spec_aux st1 st2 c c'.
  tauto.
Qed.

(* ################################################################# *)
(** * From Multi-step Relations To Denotations *)

Theorem semantic_equiv_aexp2: forall st a n,
  multi_astep st a (ANum n) -> aeval a st = n.
Proof.
  intros.
  revert n H; induction a; intros; simpl.
  + apply ANum_halt in H.
    injection H as ?H.
    rewrite H.
    reflexivity.
  + unfold_with_1n multi_astep in H.
    inversion H; subst.
    inversion H0; subst.
    inversion H1; subst.
    - reflexivity.
    - inversion H2.
  + apply APlus_path_spec in H.
    destruct H as [n1 [n2 [? [? ?]]]].
    apply IHa1 in H.
    apply IHa2 in H0.
    unfold Func.add; lia.
  + apply AMinus_path_spec in H.
    destruct H as [n1 [n2 [? [? ?]]]].
    apply IHa1 in H.
    apply IHa2 in H0.
    unfold Func.sub; lia.
  + apply AMult_path_spec in H.
    destruct H as [n1 [n2 [? [? ?]]]].
    apply IHa1 in H.
    apply IHa2 in H0.
    unfold Func.mul; nia.
Qed.

Theorem semantic_equiv_bexp2: forall st b,
  (multi_bstep st b BTrue -> beval b st) /\
  (multi_bstep st b BFalse -> ~ beval b st).
Proof.
  intros.
  induction b; simpl.
  + split; intros.
    - exact I.
    - apply never_BTrue_to_BFalse in H.
      destruct H.
  + split; intros.
    - apply never_BFalse_to_BTrue in H.
      destruct H.
    - tauto.
  + split; intros.
    - apply BEq_True_path_spec in H.
      destruct H as [n1 [n2 [? [? ?]]]].
      apply semantic_equiv_aexp2 in H.
      apply semantic_equiv_aexp2 in H0.
      unfold Func.test_eq; lia.
    - apply BEq_False_path_spec in H.
      destruct H as [n1 [n2 [? [? ?]]]].
      apply semantic_equiv_aexp2 in H.
      apply semantic_equiv_aexp2 in H0.
      unfold Func.test_eq; lia.
  + split; intros.
    - apply BLe_True_path_spec in H.
      destruct H as [n1 [n2 [? [? ?]]]].
      apply semantic_equiv_aexp2 in H.
      apply semantic_equiv_aexp2 in H0.
      unfold Func.test_le; lia.
    - apply BLe_False_path_spec in H.
      destruct H as [n1 [n2 [? [? ?]]]].
      apply semantic_equiv_aexp2 in H.
      apply semantic_equiv_aexp2 in H0.
      unfold Func.test_le; lia.
  + destruct IHb as [IHb1 IHb2].
    split; intros.
    - apply BNot_True_path_spec in H.
      unfold Sets.complement; tauto.
    - apply BNot_False_path_spec in H.
      unfold Sets.complement; tauto.
  + split; intros.
    - apply BAnd_True_path_spec in H.
      unfold Sets.intersect; tauto.
    - apply BAnd_False_path_spec in H.
      unfold Sets.intersect; tauto.
Qed.

Theorem semantic_equiv_com2: forall c st1 st2,
  multi_cstep (c, st1) (CSkip, st2) -> ceval c st1 st2.
Proof.
  intros.
  revert st1 st2 H; induction c; intros.
  + apply CSkip_halt in H.
    destruct H.
    rewrite H0.
    simpl.
    unfold BinRel.id.
    reflexivity.
  + apply CAss_path_spec in H.
    destruct H as [n [? [? ?]]].
    apply semantic_equiv_aexp2 in H.
    rewrite ceval_CAss, H.
    tauto.
  + apply CSeq_path_spec in H.
    destruct H as [st1' [? ?]].
    apply IHc1 in H.
    apply IHc2 in H0.
    rewrite ceval_CSeq.
    unfold BinRel.concat.
    exists st1'.
    tauto.
  + apply CIf_path_spec in H.
    rewrite ceval_CIf.
    unfold if_sem.
    unfold BinRel.union,
           BinRel.concat,
           BinRel.test_rel.
    specialize (IHc1 st1 st2).
    specialize (IHc2 st1 st2).
    pose proof semantic_equiv_bexp2 st1 b.
    destruct H; [left | right]; exists st1; tauto.
  + apply CWhile_path_spec in H.
    rewrite ceval_CWhile.
    unfold loop_sem.
    unfold BinRel.omega_union.
    destruct H as [n ?].
    exists n.
    revert st1 H; induction n; simpl; intros.
    - pose proof semantic_equiv_bexp2 st1 b.
      destruct H.
      subst st2.
      unfold BinRel.test_rel,
             Sets.complement.
      tauto.
    - destruct H as [st1' [? [? ?]]].
      specialize (IHn st1').
      unfold BinRel.concat,
             BinRel.test_rel.
      apply semantic_equiv_bexp2 in H.
      exists st1.
      split.
      * tauto.
      * exists st1'.
        specialize (IHc st1 st1').
        tauto.
Qed.

(* ################################################################# *)
(** * Final Theorem *)

Theorem semantic_equiv: forall c st1 st2,
  ceval c st1 st2 <-> multi_cstep (c, st1) (CSkip, st2).
Proof.
  intros.
  split.
  + apply semantic_equiv_com1.
  + apply semantic_equiv_com2.
Qed.

(* ################################################################# *)
(** * Alternative Proofs: From Multi-step Relations To Denotations *)

Lemma aeval_preserve: forall st a1 a2,
  astep st a1 a2 ->
  aeval a1 st  = aeval a2 st.
Proof.
  intros.
  induction H.
  + simpl.
    reflexivity.
  + simpl.
    unfold Func.add.
    lia.
  + simpl.
    unfold Func.add.
    lia.
  + simpl.
    unfold Func.add, constant_func.
    reflexivity.
  + simpl.
    unfold Func.sub.
    lia.
  + simpl.
    unfold Func.sub.
    lia.
  + simpl.
    unfold Func.sub, constant_func.
    reflexivity.
  + simpl.
    unfold Func.mul.
    nia.
  + simpl.
    unfold Func.mul.
    nia.
  + simpl.
    unfold Func.mul, constant_func.
    reflexivity.
Qed.

Lemma beval_preserve: forall st b1 b2,
  bstep st b1 b2 ->
  (beval b1 st  <-> beval b2 st).
Proof.
  intros.
  induction H.
  + apply aeval_preserve in H.
    simpl.
    unfold Func.test_eq.
    lia.
  + apply aeval_preserve in H0.
    simpl.
    unfold Func.test_eq.
    lia.
  + simpl.
    unfold Func.test_eq, Sets.full.
    tauto.
  + simpl.
    unfold Func.test_eq, Sets.empty.
    tauto.
  + apply aeval_preserve in H.
    simpl.
    unfold Func.test_le.
    lia.
  + apply aeval_preserve in H0.
    simpl.
    unfold Func.test_le.
    lia.
  + simpl.
    unfold Func.test_le, Sets.full.
    tauto.
  + simpl.
    unfold Func.test_le, constant_func, Sets.empty.
    lia.
  + simpl.
    unfold Sets.complement.
    tauto.
  + simpl.
    unfold Sets.complement, Sets.full, Sets.empty.
    tauto.
  + simpl.
    unfold Sets.complement, Sets.full, Sets.empty.
    tauto.
  + simpl.
    unfold Sets.intersect.
    tauto.
  + simpl.
    unfold Sets.intersect, Sets.full.
    tauto.
  + simpl.
    unfold Sets.intersect, Sets.empty.
    tauto.
Qed.

Lemma ceval_preserve: forall c1 c2 st1 st2,
  cstep (c1, st1) (c2, st2) ->
  forall st3, ceval c2 st2 st3 -> ceval c1 st1 st3.
Proof.
(** We could prove a stronger conclusion:

    forall st3, ceval c1 st1 st3 <-> ceval c2 st2 st3.

But this single direction version is enough to use. *)
  intros.
  revert H0.
  remember (c1, st1) as cst1 eqn:H0.
  remember (c2, st2) as cst2 eqn:H1.
  revert c1 c2 st1 st2 st3 H0 H1; induction H; simpl; intros.
  + apply aeval_preserve in H.
    injection H0 as ? ?.
    injection H1 as ? ?.
    subst.
    rewrite ceval_CAss in H2.
    rewrite ceval_CAss.
    rewrite H.
    tauto.
  + injection H1 as ? ?.
    injection H2 as ? ?.
    subst.
    rewrite ceval_CSkip in H3.
    rewrite ceval_CAss.
    unfold BinRel.id in H3.
    subst.
    tauto.
  + injection H0 as ? ?.
    injection H1 as ? ?.
    subst.
    rewrite ceval_CSeq in H2.
    rewrite ceval_CSeq.
    unfold BinRel.concat in H2.
    unfold BinRel.concat.
    destruct H2 as [st2' [? ?]].
    exists st2'.
    assert ((c1, st1) = (c1, st1)). { reflexivity. }
    assert ((c1', st2) = (c1', st2)). { reflexivity. }
    specialize (IHcstep _ _ _ _ st2' H2 H3).
    tauto.
  + injection H0 as ? ?.
    injection H1 as ? ?.
    subst.
    simpl.
    unfold BinRel.concat, BinRel.id.
    exists st2.
    split.
    - reflexivity.
    - exact H2.
  + injection H0 as ? ?.
    injection H1 as ? ?.
    subst.
    rewrite ceval_CIf in H2.
    rewrite ceval_CIf.
    unfold if_sem in H2.
    unfold if_sem.
    unfold BinRel.union,
           BinRel.concat,
           BinRel.test_rel in H2.
    unfold BinRel.union,
           BinRel.concat,
           BinRel.test_rel.
    apply beval_preserve in H.
    simpl in H2.
    simpl.
    unfold Sets.complement in H2.
    unfold Sets.complement.
    destruct H2 as [[st2' ?] | [st2' ?]]; [left | right];
      exists st2'; tauto.
  + injection H0 as ? ?.
    injection H1 as ? ?.
    subst.
    rewrite ceval_CIf.
    unfold if_sem.
    unfold BinRel.union,
           BinRel.concat,
           BinRel.test_rel.
    left; exists st2; simpl.
    unfold Sets.full; tauto.
  + injection H0 as ? ?.
    injection H1 as ? ?.
    subst.
    rewrite ceval_CIf.
    unfold if_sem.
    unfold BinRel.union,
           BinRel.concat,
           BinRel.test_rel.
    right; exists st2; simpl.
    unfold Sets.complement, Sets.empty; tauto.
  + injection H0 as ? ?.
    injection H1 as ? ?.
    subst.
    pose proof loop_unrolling b c.
    unfold com_equiv, BinRel.equiv in H.
    specialize (H st2 st3).
    tauto.
Qed.

End DenotationSmallStep.

Module OneBinRel_FOL.

Definition logical_var: Type := nat.

Inductive term: Type :=
| TId (v: logical_var): term.

Inductive prop: Type :=
| PEq (t1 t2: term): prop
| PRel (t1 t2: term): prop
| PFalse: prop
| PImpl (P Q: prop): prop
| PForall (x: logical_var) (P: prop): prop.

Definition PTrue: prop := PImpl PFalse PFalse.
Definition PNot (P: prop): prop := PImpl P PFalse.
Definition PAnd (P Q: prop): prop := PNot (PImpl P (PNot Q)). 
Definition POr (P Q: prop): prop := PImpl (PNot P) Q. 
Definition PExists (x: logical_var) (P: prop): prop :=
  PNot (PForall x (PNot P)).

Bind Scope FOL_scope with prop.
Delimit Scope FOL_scope with FOL.

Coercion TId: logical_var >-> term.
Notation "x = y" := (PEq x y) (at level 70, no associativity) : FOL_scope.
Notation "P1 'OR' P2" := (POr P1 P2) (at level 76, left associativity) : FOL_scope.
Notation "P1 'AND' P2" := (PAnd P1 P2) (at level 74, left associativity) : FOL_scope.
Notation "P1 'IMPLY' P2" := (PImpl P1 P2) (at level 77, right associativity) : FOL_scope.
Notation "'NOT' P" := (PNot P) (at level 73, right associativity) : FOL_scope.
Notation "'EXISTS' x ',' P " := (PExists x ((P)%FOL)) (at level 79,  right associativity) : FOL_scope.
Notation "'FORALL' x ',' P " := (PForall x ((P)%FOL)) (at level 79, right associativity) : FOL_scope.

Definition term_rename (x y: logical_var) (t: term) :=
    match t with
    | TId x' => 
        if Nat.eq_dec x x'
        then TId y
        else TId x'
    end.

Fixpoint prop_rename (x y: logical_var) (d: prop): prop :=
    match d with
    | PEq t1 t2    => PEq (term_rename x y t1) (term_rename x y t2)
    | PRel t1 t2   => PRel (term_rename x y t1) (term_rename x y t2)
    | PImpl P1 P2  => PImpl (prop_rename x y P1) (prop_rename x y P2)
    | PFalse       => PFalse
    | PForall x' P => if Nat.eq_dec x x'
                      then PForall x' P
                      else PForall x' (prop_rename x y P)
    end.

Definition term_max_var (t: term): logical_var :=
    match t with
    | TId x => x
    end.

Fixpoint prop_max_var (d: prop): logical_var :=
    match d with
    | PEq t1 t2    => max (term_max_var t1) (term_max_var t2)
    | PRel t1 t2   => max (term_max_var t1) (term_max_var t2)
    | PFalse       => O
    | PImpl P1 P2  => max (prop_max_var P1) (prop_max_var P2)
    | PForall x' P => max x' (prop_max_var P)
    end.

Definition new_var (P: prop) (t: term): logical_var :=
  S (max (prop_max_var P) (term_max_var t)).

Definition term_occur (x: logical_var) (t: term): nat :=
    match t with
    | TId x' => if Nat.eq_dec x x' then S O else O
    end.

Fixpoint prop_free_occur (x: logical_var) (d: prop): nat :=
    match d with
    | PEq t1 t2    => (term_occur x t1) + (term_occur x t2)
    | PRel t1 t2   => (term_occur x t1) + (term_occur x t2)
    | PFalse       => O
    | PImpl P1 P2  => (prop_free_occur x P1) + (prop_free_occur x P2)
    | PForall x' P => if Nat.eq_dec x x'
                      then O
                      else prop_free_occur x P
    end.

Fixpoint rename_all (t: term) (d: prop): prop :=
    match d with
    | PEq t1 t2   => PEq t1 t2
    | PRel t1 t2  => PRel t1 t2
    | PFalse      => PFalse
    | PImpl P1 P2 => PImpl (rename_all t P1) (rename_all t P2)
    | PForall x P => match term_occur x t with
                        | O => PForall x (rename_all t P)
                        | _ => PForall
                                 (new_var (rename_all t P) t)
                                 (prop_rename x
                                   (new_var (rename_all t P) t)
                                   (rename_all t P))
                        end
    end.

Definition term_sub (x: logical_var) (tx: term) (t: term) :=
    match t with
    | TId x' =>
         if Nat.eq_dec x x'
         then tx
         else TId x'
    end.

Fixpoint naive_sub (x: logical_var) (tx: term) (d: prop): prop :=
    match d with
    | PEq t1 t2   => PEq (term_sub x tx t1) (term_sub x tx t2)
    | PRel t1 t2  => PRel (term_sub x tx t1) (term_sub x tx t2)
    | PFalse      => PFalse
    | PImpl P1 P2 => PImpl (naive_sub x tx P1) (naive_sub x tx P2)
    | PForall x P => PForall x (naive_sub x tx P)
    end.

Definition prop_sub (x: logical_var) (tx: term) (P: prop): prop :=
  naive_sub x tx (rename_all tx P).

Notation "P [ x |-> t ]" := (prop_sub x t ((P)%FOL)) (at level 10, x at next level) : FOL_scope.

Inductive provable: prop -> Prop :=
| PImply_1: forall P Q, provable (P IMPLY (Q IMPLY P))
| PImply_2: forall P Q R, provable
   ((P IMPLY Q IMPLY R) IMPLY
    (P IMPLY Q) IMPLY
    (P IMPLY R))
| Modus_ponens: forall P Q,
    provable (P IMPLY Q) ->
    provable P ->
    provable Q
| PFalse_elim: forall P,
    provable (PFalse IMPLY P)
| Excluded_middle: forall P,
    provable (NOT P OR P)
| PForall_elim: forall x t P,
    provable ((FORALL x, P) IMPLY (P [x |-> t]))
| PForall_intros: forall x P Q,
    prop_free_occur x P = O ->
    provable (P IMPLY Q) ->
    provable (P IMPLY FORALL x, Q)
| PEq_refl: forall t,
    provable (t = t)
| PEq_sub: forall P x t t',
    provable (t = t' IMPLY P[x |-> t] IMPLY P[x |-> t']).

Notation "|--  P" := (provable P) (at level 91, no associativity): FOL_scope.

(** We can formalize its semantics as follows. First, an interpretation is a
domain [D], an interpretation [Rel] of the binary relation symbol [PRel] and
assignments of all logical variables.*)

Inductive Interp: Type :=
| Build_Interp (D: Type) (Rel: D -> D -> Prop) (La: logical_var -> D) : Interp.

Definition domain_of (J: Interp): Type :=
  match J with
  | Build_Interp D _ _ => D
  end.

Definition Rel_of (J: Interp): domain_of J -> domain_of J -> Prop :=
  match J as J0 return
    match J0 with
    | Build_Interp D Rel La => D
    end ->
    match J0 with
    | Build_Interp D Rel La => D
    end ->
    Prop
  with
  | Build_Interp D Rel La => Rel
  end.

Definition Lassn_of (J: Interp): logical_var -> domain_of J :=
  match J as J0 return
    logical_var -> 
    match J0 with
    | Build_Interp D Rel La => D
    end
  with
  | Build_Interp D Rel La => La
  end.

Definition Lassn_update {D: Type} (La: logical_var -> D) (x: logical_var) (v: D): logical_var -> D :=
  fun y => if (Nat.eq_dec x y) then v else La y.

Definition Interp_Lupdate (J: Interp) (x: logical_var): domain_of J -> Interp :=
  match J with
  | Build_Interp D Rel La =>
     fun v => Build_Interp D Rel (Lassn_update La x v)
  end.

Definition term_denote (J: Interp) (t: term): domain_of J :=
    match t with
    | TId x => Lassn_of J x
    end.

Fixpoint satisfies (J: Interp) (d: prop): Prop :=
    match d with
    | PEq t1 t2   => (term_denote J t1 = term_denote J t2)
    | PRel t1 t2  => Rel_of J (term_denote J t1) (term_denote J t2)
    | PFalse      => False
    | PImpl P1 P2 => ~ (satisfies J P1) \/ (satisfies J P2)
    | PForall x P => forall v, satisfies (Interp_Lupdate J x v) P
    end.

Notation "J  |==  x" := (satisfies J x) (at level 90, no associativity): FOL_scope.

Local Open Scope FOL_scope.

Definition valid (P: prop): Prop :=
  forall J: Interp, J |== P.

Notation "|==  P" := (valid P) (at level 91, no associativity): FOL_scope.

Definition sound: Prop :=
  forall P: prop, |-- P -> |== P.

Definition complete: Prop :=
  forall P: prop, |== P -> |-- P.

Lemma prop_sub_spec: forall J (P: prop) (x: logical_var) (t: term),
  J |== P[ x |-> t] <->
  Interp_Lupdate J x (term_denote J t) |== P.
Admitted.

Lemma no_occ_satisfies: forall J P x v,
  prop_free_occur x P = O ->
  (J |== P <-> Interp_Lupdate J x v |== P).
Admitted.

End OneBinRel_FOL.

(* 2021-02-21 23:59 *)
