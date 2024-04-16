From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
(* From Coq Require Import ZArith. *)
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Extraction.
From Coq Require Import Lia.
From Coq Require Import Program.
From Coq Require Import Program.Wf.
From Coq Require Import Strings.String.
Set Implicit Arguments.
Open Scope string_scope.

Section Defs.
  Context {A : Type}.
  Definition relation := A -> A -> Prop.


  Class Reflexive (R : relation) := refl : forall x, R x x.

  Class Transitive (R : relation) :=
    trans : forall x y z, R x y -> R y z -> R x z.

  Class Antisymmetry (R : relation) :=
    anti_sym : forall x y, R x y -> R y x -> x = y.

  Class Completeness (R : relation) :=
    comp : forall x y, R x y \/ R y x.


  Class Quasi_Order (R : relation) : Prop := {
      qo_refl :: Reflexive R;
      qo_trans :: Transitive R;
    }.

  Class Partial_Order (R : relation) : Prop := {
      po_qo :: Quasi_Order R;
      po_anti_sym :: Antisymmetry R;
    }.

  Class Total_Order (R : relation) : Prop := {
      to_po :: Partial_Order R;
      to_comp :: Completeness R;
    }.
End Defs.

Search (_ < _).

Section Nat_TO.

  Lemma le_dec' : forall n m, n <= m \/ m <= n.
    Proof. lia. Qed.

  Instance Le_Refl : Reflexive le := le_refl.
  Instance Le_Trans : Transitive le := le_trans.
  Instance Le_Anti_Sym : Antisymmetry le := le_antisymm.
  Instance Le_Comp : Completeness le := le_dec'.

  Instance Le_QO : Quasi_Order le := { }.
  Instance Le_PO : Partial_Order le := { }.
  Instance Le_TO : Total_Order le := { }.

End Nat_TO.

Section Ext_Nat_TO.

  Inductive ext_nat : Set :=
  | ENat:  forall n : nat, ext_nat
  | EInf : ext_nat.

  Inductive en_le : ext_nat -> ext_nat -> Prop :=
  | en_le_nat : forall n m : nat, n <= m -> (en_le (ENat n) (ENat m))
  | en_le_inf : forall n : ext_nat, (en_le n EInf).

  Notation "n '<=e' m" := (en_le n m) (at level 50).
  Notation "n '<e' m" := (en_le n m /\ n <> m) (at level 50).

  Definition en_ge := fun (n m : ext_nat) => (m <=e n).

  Notation "n '>=e' m" := (en_ge n m) (at level 50).
  Notation "n '>e' m" := (en_ge n m /\ n <> m) (at level 50).

  Definition en_eqb (n m : ext_nat) : bool :=
  match n, m with
  | ENat n', ENat m' => Nat.eqb n' m'
  | EInf, EInf => true
  | _, _ => false
  end.

  Notation "n '=?e' m" := (en_eqb n m) (at level 99).

  Lemma en_le_le : forall n m : nat, ENat n <=e ENat m -> n <= m.
  Proof. intros. inversion H. lia. Qed.

  Lemma en_ge_ge : forall n m : nat, ENat n >=e ENat m -> n >= m.
  Proof. intros. inversion H. lia. Qed.

  Lemma en_neq_neq : forall n m : nat, ENat n <> ENat m -> n <> m.
  Proof. intros n m H. unfold not in H. unfold not. intros H'. apply (f_equal ENat) in H'. apply H in H'. assumption.
  Qed.

  Lemma en_lt_lt : forall n m : nat, ENat n <e ENat m -> n < m.
  Proof. intros. inversion H. inversion H0. apply en_neq_neq in H1. lia. Qed.

  Lemma en_gt_gt : forall n m : nat, ENat n >e ENat m -> n > m.
  Proof. intros. inversion H. inversion H0. apply en_neq_neq in H1. lia. Qed.

  Lemma gt_en_gt : forall n m : nat, n > m -> ENat n >e ENat m.
  Proof. intros n m H. unfold en_ge. split.
  - apply en_le_nat. lia.
  - unfold not. intros. injection H0. intros. lia.
  Qed.

  Lemma einf_gt_nat : forall n : nat, EInf >e ENat n.
  Proof. intros n. unfold en_ge. split. apply en_le_inf. unfold not. intros. discriminate.
  Qed.

  Ltac enatlia :=
    intros;
    repeat match goal with
    | [H : ext_nat |- _] => destruct H
    | [H : ENat _ <=e ENat _ |- _] => apply en_le_le in H
    | [H : EInf <=e ENat _ |- _] => inversion H
    | [H : ENat _ <> ENat _ |- _] => apply en_neq_neq in H
    | [H : ENat _ >=e ENat _ |- _] => apply en_ge_ge in H
    | [H : ENat _ >=e EInf |- _] => inversion H
    | [H : ENat _ <e ENat _ |- _] => apply en_lt_lt in H
    | [H : EInf _ <e ENat _ |- _] => inversion H
    | [H : ENat _ >e ENat _ |- _] => apply en_gt_gt in H
    | [H : ENat _ >e EInf |- _] => inversion H
    | [|- ENat _ >e ENat _] => apply gt_en_gt
    | [|- EInf >e ENat _] => apply einf_gt_nat
    | [H : EInf = ENat _ |- _] => inversion H
    | [|- ENat _ = ENat _] => f_equal
    | [|- EInf = EInf] => trivial
    end;
    try (apply en_le_nat); try (apply en_le_inf); try lia.

  Example enat_test: (ENat 1) <=e (ENat 1).
  apply en_le_nat. apply le_n. Qed.

  Lemma en_le_refl : forall w : ext_nat, w <=e w.
  Proof. enatlia. Qed.

  Lemma en_le_trans : forall u v w : ext_nat, u <=e v -> v <=e w -> u <=e w.
  Proof. enatlia. Qed.

  Lemma po_enat : forall (a b : ext_nat), a <=e b -> b <=e a -> a = b.
    Proof. enatlia. Qed.

  Lemma to_enat : forall a b, a <=e b \/ b <=e a.
  Proof.
    intros. destruct a, b. assert (n <= n0 \/ n0 <= n) by (apply Le_Comp).
    destruct H.
    - left. enatlia.
    - right. enatlia.
    - left. enatlia.
    - right. enatlia.
    - left. enatlia.
  Qed.

  Instance En_Le_Refl : Reflexive en_le := en_le_refl.
  Instance En_Le_Trans : Transitive en_le := en_le_trans.
  Instance En_Le_AntiSym : Antisymmetry en_le := po_enat.
  Instance En_Le_Comp : Completeness en_le := to_enat.

  Instance En_Le_QO : Quasi_Order en_le := { }.
  Instance En_Le_PO : Partial_Order en_le := { }.
  Instance En_Le_TO : Total_Order en_le := { }.

End Ext_Nat_TO.
