From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Bool.Bool.
Set Implicit Arguments.

Section Seq_Sec.
  Variable A : Type.

  CoInductive Seq : Type := Cons : A -> Seq -> Seq.

  Definition hd (s : Seq) : A   := match s with Cons x _ => x end.
  Definition tl (s : Seq) : Seq := match s with Cons _ t => t end.
End Seq_Sec.

Section Sub_Seq_Sec.
  Variable A B : Type.

  Inductive suffix : Seq A -> Seq A -> Prop :=
  | sf_eq   : forall s, suffix s s
  | sf_next : forall (s1 s2 : Seq A) (x : A), suffix s1 s2 -> suffix s1 (Cons x s2).

  Inductive sub_seq : Seq A -> Seq A -> Prop :=
  | ss_sf : forall s1 s2, suffix s1 s2 -> sub_seq s1 s2
  | ss_hd : forall s1 s2, hd s1 = hd s2 -> sub_seq (tl s1) (tl s2)
  | ss_tl : forall s1 s2, hd s1 <> hd s2 -> sub_seq s1      (tl s2).

  CoFixpoint map (f : A -> B) (s : Seq A) : Seq B :=
    match s with
    | Cons hd tl => Cons (f hd) (map f tl)
    end.

  Fixpoint drop (n : nat) (s : Seq A) : Seq A :=
    match n with
    | O    => s
    | S n' => match s with Cons hd tl => drop n' tl end
    end.

  Inductive fin_sub_seq : list A -> Seq A -> Prop :=
  | empty : forall s, fin_sub_seq [] s
  | n_empty : forall hd tl s, exists x s', s' = drop x s /\ (match s' with Cons h t => h = hd /\ fin_sub_seq tl t -> fin_sub_seq (hd::tl) s).
