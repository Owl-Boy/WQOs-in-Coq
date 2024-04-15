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

Search Nat.leb.

Class Quasi_Order (A : Type) := {
    ord : A -> A -> Prop;
    refl_axiom : forall a, ord a a;
    trans_axiom : forall a b c, ord a b -> ord b c -> ord a c
  }.

Notation "a '<=qo' b" := (ord a b) (at level 50).
Notation "a '<qo' b" := (ord a b /\ a <> b) (at level 50).

Class Partial_Order (A : Type) `{Quasi_Order A} := {
    anti_sym_axiom : forall a b, a <=qo b -> b <=qo a -> a = b
  }.

Class Total_Order (A : Type) `{Partial_Order A} := {
    total_order_axiom : forall a b, a <=qo b \/ b <=qo a
  }.


Search (_ <= _).

Section Nat_QO.
  Lemma le_dec' : forall n m, n <= m \/ m <= n.
    Proof. lia. Qed.

  Instance QONat : Quasi_Order nat :=
    {
      ord := le;
      refl_axiom := le_refl;
      trans_axiom := le_trans;
    }.

  Instance PONat: Partial_Order :=
    { anti_sym_axiom := Nat.le_antisymm; }.

  Instance TONat: Total_Order :=
    { total_order_axiom := le_dec'; }.
End Nat_QO.

Section Ext_Nat_QO.
  Inductive ext_nat : Set :=
  | ENat:  forall n : nat, ext_nat
  | EInf : ext_nat
  .

  Inductive en_le : ext_nat -> ext_nat -> Prop :=
  | en_le_nat : forall n m : nat, n <= m -> (en_le (ENat n) (ENat m))
  | en_le_inf : forall n : ext_nat, (en_le n EInf)
  .

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

  Instance QOENat : Quasi_Order ext_nat :=
    {
      ord := en_le;
      refl_axiom := en_le_refl;
      trans_axiom := en_le_trans;
    }.

  Lemma po_enat : forall (a b : ext_nat), a <=e b -> b <=e a -> a = b.
    Proof. enatlia. Qed.

  Instance POENat : Partial_Order :=
    { anti_sym_axiom := po_enat }.

  Check total_order_axiom 1.

  Lemma to_enat `{Total_Order}: forall (a b : ext_nat), a <=e b \/ b <=e a.
    Proof. intros. destruct a, b. assert (n <= n0 \/ n0 <= n).
           assert (total_order_axiom n n0).

  Instance TOENat : Total_Order :=
    {  }


  (* Instance QONat : Quasi_Order nat := *)

  (*   { *)
  (*     ord := le; *)
  (*     refl_axiom := le_refl; *)
  (*     trans_axiom := le_trans; *)
  (*   }. *)

  (* Instance PONat: Partial_Order := *)
  (*   { anti_sym_axiom := Nat.le_antisymm; }. *)

  (* Instance TONat: Total_Order := *)
  (*   { total_order_axiom := le_dec'; }. *)












(* Stay Away for now *)

Definition inj (f : nat -> nat) := forall x y, f x = f y -> x = y.

Definition wqo_axiom1 (A : Type) `{Quasi_Order A} : Prop :=
  forall (f : nat -> A), exists x y, (f x) <=qo (f y).

Definition increasing {A : Type} `{Quasi_Order A} (f : nat -> A) :=
  forall x y, x < y -> (f x) <=qo (f y).

Definition wqo_axiom2 (A : Type) `{Quasi_Order A} : Prop :=
  forall (f : nat -> A), exists (f' : nat -> nat),
    inj f' /\ increasing (fun n => f (f' n)).

Definition anti_chain {A : Type} `{Quasi_Order A} (f : nat -> A) :=
  forall x y, x <> y -> ~((f x) <=qo (f y)) /\ ~((f y) <=qo (f x)).

Definition descending {A : Type} `{Quasi_Order A} (f : nat -> A) :=
  forall x y, x < y -> ((f y) <=qo (f x)) /\ f x <> f y.

Definition wqo_axiom3 (A : Type) `{Quasi_Order A} : Prop :=
  forall (f : nat -> A), ~(exists f' : nat ->  nat, inj f' /\ (anti_chain (fun n => f (f' n))
                                          \/ descending (fun n => f (f' n)))).

Theorem wqo_equiv (A : Type) `{Quasi_Order A} : (wqo_axiom1 -> wqo_axiom2)
                                              /\ (wqo_axiom2 -> wqo_axiom3)
                                              /\ (wqo_axiom3 -> wqo_axiom1).
  unfold wqo_axiom1, wqo_axiom2, wqo_axiom3.
  repeat (split; intros).
  Admitted.
