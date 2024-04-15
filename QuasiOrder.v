(* From Coq Require Import QArith.
From Coq Require Import Reals.
Print IR.
Print IZ. *)

Require Import Lia.
Require Import Nat.
Print LoadPath.
Require Import PHP.


Module WSTSPlayground.

Create HintDb wstshints.

Record QO : Type := mkQO
{
	carrier : Set;
	ord : carrier -> carrier -> Prop;
	qo_refl : forall s : carrier, ord s s;
	qo_trans : forall s t u : carrier, (ord s t) -> (ord t u) -> (ord s u);
}.

Notation "a '<=qo' b" := (ord _ a b) (at level 50).
Notation "a '<qo' b" := (ord _ a b /\ a <> b) (at level 50).

Inductive ext_nat : Set :=
| ENat:  forall n : nat, ext_nat
| EInf : ext_nat
.

Check le.
Check le_n.


Inductive en_le : ext_nat -> ext_nat -> Prop :=
| en_le_nat : forall n m : nat, n <= m -> (en_le (ENat n) (ENat m))
| en_le_inf : forall n : ext_nat, (en_le n EInf)
.

Print gt.

Notation "n '<=e' m" := (en_le n m) (at level 50).
Notation "n '<e' m" := (en_le n m /\ n <> m) (at level 50).

Definition en_ge := fun (n m : ext_nat) => (m <=e n).

Notation "n '>=e' m" := (en_ge n m) (at level 50).
Notation "n '>e' m" := (en_ge n m /\ n <> m) (at level 50).

Definition en_eqb (n m : ext_nat) : bool :=
match n, m with
| ENat n', ENat m' => eqb n' m'
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
	end;
	try (apply en_le_nat); try (apply en_le_inf); try lia.

Example enat_test: (ENat 1) <=e (ENat 1).
apply en_le_nat. apply le_n. Qed.

Lemma en_le_refl : forall w : ext_nat, w <=e w.
Proof. enatlia. Qed.

Lemma en_le_trans : forall u v w : ext_nat, u <=e v -> v <=e w -> u <=e w.
Proof. enatlia. Qed.

Definition enat_qo :=
	{|	carrier := ext_nat;
	 		ord := en_le;
			qo_refl := en_le_refl;
			qo_trans := en_le_trans |}.

Definition seq (A : Set) : Set := nat -> A.

Definition iden : (seq nat) := (fun n => n).

Definition only_1_shall_pass (n : ext_nat) : Prop :=
match n with
| ENat 1 => True
| _ => False
end.


Definition is_antichain (L : QO) (P : carrier L -> Prop) : Prop :=
forall (x y : carrier L), ((x <> y) /\ (P x /\ P y)) -> ~( (ord L x y) \/ (ord L y x) ).

Lemma test : is_antichain enat_qo only_1_shall_pass.
Proof. unfold is_antichain. intros x y H. unfold not. intros H1.
destruct H. destruct H0. unfold only_1_shall_pass in *. destruct x; destruct y; enatlia. destruct n; destruct n0; auto.
destruct n; destruct n0; auto.
Qed.

Definition is_well_founded (L : QO) := forall ni : (seq (carrier L)),
	exists i : nat,
		exists j : nat,
			i < j /\ (ni i) <=qo (ni j).

#[local] Hint Unfold is_well_founded : wstshints.

Axiom lem : forall P : Prop, P \/ ~P.
Axiom dne : forall P : Prop, ~~P -> P.
Axiom not_forall_exists : forall S : Set, forall P : S -> Prop, ~ (forall x, P x) -> exists x, ~ P x.

Definition enat_increasing (f : nat -> ext_nat) := forall n m : nat, n < m -> f n <e f m.

Definition nat_qo :=
{|	carrier := nat;
		ord := le;
		qo_refl := le_n;
		qo_trans := PeanoNat.Nat.le_trans;
|}.



Ltac notHyp P :=
  match goal with
    | [ _ : P |- _ ] => fail 1
    | _ =>
      match P with
        | ?P1 /\ ?P2 => first [ notHyp P1 | notHyp P2 | fail 2 ]
        | _ => idtac
      end
  end.


Ltac extend pf :=
  let t := type of pf in
    notHyp t; generalize pf; intro.


Ltac complete :=
  repeat match goal with
           | [ |- _ /\ _ ] => constructor
           | [ H : _ /\ _ |- _ ] => destruct H
					 | [ H : _ \/ _ |- _] => destruct H
           | [ H : ?P -> ?Q, H' : ?P |- _ ] => specialize (H H')
           | [ |- forall x, _ ] => intro

           | [ H : forall x, ?P x -> _, H' : ?P ?X |- _ ] => extend (H X H')
         end.



Lemma lem_le : forall n m : nat, n < m \/ n >= m.
Proof. lia. Qed.

Lemma trichotomy : 
	forall n m : nat, n < m \/ n = m \/ n > m. 
Proof. lia. Qed.

Ltac tlia :=
	intros;
	complete;
	subst;
	repeat match goal with
	| [n : nat, m : nat |- _] => 
		notHyp (n < m); notHyp (n = m); notHyp (n > m);
		notHyp (m < n); notHyp (m > n); idtac n; idtac n;
		generalize (trichotomy n m);
		intro;
		complete;
		subst
	| [f : nat -> nat |- _] =>
		repeat match goal with
		| [n : nat, m : nat |- _] =>
			notHyp ((f n) < m); notHyp ((f n) = m); notHyp ((f n) > m);
			notHyp (m < (f n)); notHyp (m > (f n));
			idtac n; idtac m;
			generalize (trichotomy (f n) m);
			intro;
			complete;
			subst
		end
	end;
	subst; complete.

Lemma fin' : forall n m : nat, forall f : nat -> nat, finmap n m f \/ ~(finmap n m f).
Proof. unfold finmap. intros. induction n as [| n IH].
- left. tlia; lia.
- destruct IH as [IH | IH].
	+ tlia. Abort.





Lemma fin_or_not_fin : forall n m : nat, forall f : nat -> nat, finmap n m f \/ ~(finmap n m f).
Proof. unfold finmap. intros. induction n as [| n IH].
- left. lia.
- destruct IH as [IH | IH].
	+ assert (f n < m \/ f n >= m) by lia.
		destruct H as [H | H].
		* left. intros i Hi. assert (i < n \/ i = n) by lia.
			destruct H0; subst; auto.
		* right. unfold not. intros. specialize H0 with n. assert (f n < m) by auto. lia.
	+ right. unfold not. intros.
		assert (forall i : nat, i < n -> f i < m) by auto.
		auto.
Qed.

Lemma fin_or_exists_counter : forall n m : nat, forall f : nat -> nat, finmap n m f \/ exists k : nat, k < n /\ f k >= m.
Proof. intros n m f. remember (fin_or_not_fin n m f) as Hfin; clear HeqHfin. destruct Hfin as [Hfin | Hfin].
- left; assumption.
- right. unfold finmap in Hfin.
	destruct m as [| m].
	+ destruct n. 
		exfalso. apply Hfin. intros i Hi. inversion Hi.
		exists 0. lia.
	+ induction n as [| n IHn].
		exfalso. apply Hfin. lia.
		specialize (fin_or_not_fin) with (S n) m f; intros [Hfin' | Hfin']; unfold finmap in Hfin'.
		* assert ((f n < S m) \/ (f n >= S m)) by lia.
			destruct H as [H | H].
			assert (forall i : nat, i < S n -> f i < S m).
			{ intros i Hi. assert (i < n \/ i = n) by lia.
				destruct H0 as [H0 | H0]. 
				specialize Hfin' with i. lia.
				subst. assumption.
			}
			contradiction.
			exists n; split; try lia.
		* specialize (fin_or_not_fin) with n (S m) f. intros [Hfin1 | Hfin1]; unfold finmap in Hfin1.
			assert (f n < S m \/ f n >= S m) by lia.
			destruct H as [H | H].
			assert (forall i : nat, i < S n -> f i < S m).
			{ intros i Hi. assert (i < n \/ i = n) by lia.
			destruct H0 as [H0 | H0]. specialize Hfin1 with i. auto.
			subst. assumption.
			}
			contradiction.
			exists n; lia.
			apply IHn in Hfin1. destruct Hfin1 as [w Hw].
			exists w. lia.
Qed.



Lemma nat_well_founded : is_well_founded nat_qo.
Proof. unfold is_well_founded. simpl. intros ni.
unfold seq in ni. remember (ni 0) as n.
specialize fin_or_exists_counter with (n+2) (n+1) ni.
intros [Hfin | Hfin].
- assert (noninj (n+2) ni).
	{ apply php with (n+1); try lia. assumption. }
	unfold noninj in H. destruct H as [i [j H]].
	assert (i < j \/ j < i) by lia.
	destruct H0 as [Hij | Hij]. 
	exists i. exists j. lia.
	exists j. exists i. lia.
- destruct Hfin as [k Hk]. assert (0 <> k).
	unfold not. intros. apply (f_equal ni) in H. subst.
	rewrite <- H in Hk. lia.
	assert (0 < k) by lia. exists 0. exists k; lia.
Qed.

(*Fixpoint inf_noninf_helper (f : nat -> ext_nat) (n : nat) : bool * (exists k, k < n /\ (f k) = EInf) :=
match n with
| 0 => if ((f 0) =?e EInf) then (true, 0) else (false, 0)
| S n' => if (f (S n') =?e EInf) then (true, (S n')) else inf_noninf_helper f n'
end.*)

Lemma fin_inf_or_noninf : forall f : nat -> ext_nat, forall n : nat, (forall i : nat, i < n -> exists m : nat, (f i) = ENat m) \/ (exists m : nat, m < n /\ (f m) = EInf).
Proof.
intros f n. induction n as [| n IHn].
- left. intros. inversion H.
- destruct IHn as [IHn | IHn].
	+ destruct (f n) eqn:Efn.
		left. intros. assert (i < n \/ i = n) as [Hi | Hi] by lia; auto.
		exists n0. subst; auto.
		right. exists n. split. lia. auto.
	+ destruct IHn as [w [Hw1 Hw2]].
		right. exists w. split. lia. auto.
Qed.

Lemma enat_well_founded : is_well_founded enat_qo.
Proof.
unfold is_well_founded. simpl.
intros ni. unfold seq in ni. destruct (ni 0) eqn:Eni0.
- specialize fin_inf_or_noninf with ni n; intros [H | H].
	+ Abort.






