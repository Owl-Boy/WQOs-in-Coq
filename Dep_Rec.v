From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import ZArith.
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
    le : A -> A -> Prop;
    refl_axiom : forall a, le a a;
    trans_axiom : forall a b c, le a b -> le b c -> le a c
  }.

Class Partial_Order (A : Type) `{Quasi_Order A} := {
    anti_sym_axiom : forall a b, le a b -> le b a -> a = b
  }.

Class Total_Order (A : Type) `{Partial_Order A} := {
    total_order_axiom : forall a b, le a b \/ le b a
  }.

Definition inj (f : nat -> nat) := forall x y, f x = f y -> x = y.

Definition wqo_axiom1 (A : Type) `{Quasi_Order A} : Prop :=
  forall (f : nat -> A), exists x y, le (f x) (f y).

Definition increasing {A : Type} `{Quasi_Order A} (f : nat -> A) :=
  forall x y, x < y -> le (f x) (f y).

Definition wqo_axiom2 (A : Type) `{Quasi_Order A} : Prop :=
  forall (f : nat -> A), exists (f' : nat -> nat),
    inj f' /\ increasing (fun n => f (f' n)).

Definition anti_chain {A : Type} `{Quasi_Order A} (f : nat -> A) :=
  forall x y, x <> y -> ~(le (f x) (f y)) /\ ~(le (f y) (f x)).

Definition descending {A : Type} `{Quasi_Order A} (f : nat -> A) :=
  forall x y, x < y -> (le (f y) (f x)) /\ f x <> f y.

Definition wqo_axiom3 (A : Type) `{Quasi_Order A} : Prop :=
  forall (f : nat -> A), ~(exists f' : nat ->  nat, inj f' /\ (anti_chain (fun n => f (f' n))
                                          \/ descending (fun n => f (f' n)))).

Theorem wqo_equiv (A : Type) `{Quasi_Order A} : (wqo_axiom1 -> wqo_axiom2)
                                              /\ (wqo_axiom2 -> wqo_axiom3)
                                              /\ (wqo_axiom3 -> wqo_axiom1).
  unfold wqo_axiom1, wqo_axiom2, wqo_axiom3.
  repeat (split; intros).
