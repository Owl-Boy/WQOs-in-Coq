From Coq Require Import Init.Nat.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
Require Import Lia.

Definition finmap (n m : nat) (f : nat -> nat) : Prop :=
    forall (i: nat), i < n -> f i < m.

Definition inj (n : nat) (f : nat -> nat) : Prop :=
    forall (i j : nat), i < n -> j < n -> f i = f j -> i = j. 

Definition noninj (n : nat) (f : nat -> nat) : Prop := 
    exists (i j : nat), i < n /\ j < n /\ f i = f j /\ i <> j.



Lemma eq_neq : forall (x n : nat), x = n \/ x <> n. 
Proof. lia.
Qed.

Lemma ind_cases : forall (x n : nat), (x < S n) -> (x < n) \/ x = n.
Proof. lia.
Qed.


Lemma image_cases: forall (f: nat -> nat) (n v: nat),
    (forall i, i < n -> f i <> v) \/ (exists i, i < n /\ f i = v).
Proof. intros f. induction n as [| n IH].
- intros. left. intros. inversion H.
- intros. remember (IH v) as IHv. clear HeqIHv. destruct IHv as [IHv|IHv].
  + remember (eq_neq (f n) v) as Hfn. clear HeqHfn. 
    destruct Hfn as [Hfn|Hfn]. right. exists n. split.
    apply Nat.lt_succ_diag_r. assumption.
    left. intros. apply ind_cases in H. destruct H as [H|H].
    apply IHv in H. assumption.
    rewrite <- H in Hfn. assumption.
  + right. destruct IHv as [w Hw]. exists w. destruct Hw as [Hw1 Hw2].
    split. apply Nat.lt_trans with n. assumption. apply Nat.lt_succ_diag_r.
    assumption.
Qed.



Theorem inj_noninj : forall n f, ~inj n f <-> noninj n f. 
Proof.
    unfold inj, noninj.
    intros n f. split. 
    - induction n as [ | n IH]; intros A. 
      + exfalso. apply A. intros. lia.
      + destruct (image_cases f n (f n)) as [C | [a [C1 C2]]].
        * assert ( ~ (inj n f)).
        { unfold inj. unfold not. intros H. apply A. 
          intros i j Hi Hj Hfeq.
          remember (ind_cases i n) as Hindi. clear HeqHindi.
          remember (ind_cases j n) as Hindj. clear HeqHindj.
          apply Hindi in Hi. apply Hindj in Hj. clear Hindi. clear Hindj.
          destruct Hi as [Hi|Hi]; destruct Hj as [Hj|Hj].
          - apply (H i j Hi Hj Hfeq).
          - apply C in Hi. rewrite Hj in Hfeq. contradiction.
          - apply C in Hj. rewrite Hi in Hfeq. 
            symmetry in Hfeq. contradiction.
          - rewrite Hj. rewrite Hi. reflexivity.
        }
          unfold inj in H. apply IH in H. 
          destruct H as [i [j H]].
          destruct H as [Hi [Hj [Hfeq Hij]]]. 
          exists i, j. repeat (try split); lia.
        * exists a, n. repeat (try split); lia.
- intros [a [b [A1 [A2 [A3 A4]]]]] B. apply A4. apply B; auto.
Qed.

Definition erase (f: nat -> nat) (i: nat) : nat -> nat := 
    fun x => if x <? i then f x else f (S x).

Lemma restr_lemma : forall f n m, finmap (S n) m f -> finmap n m f.
Proof. 
    unfold finmap. intros f n m H i Hlt. apply H. lia.
Qed. 

Lemma inj_restr_lemma : forall f n, inj (S n) f -> inj n f. 
Proof. 
    unfold inj. intros f n H a b A B C. apply H; lia.
Qed. 

Lemma range_lemma : forall f n m, finmap (S n) (S m) f -> 
    finmap n m f \/ exists i, i < S n /\ f i = m. 
Proof. 
(** My proof does not use induction, but appeals to image_cases. **)
intros. remember (image_cases f (S n) m) as imc. clear Heqimc.
destruct imc as [imc1|imc2].
- left. unfold finmap in H. unfold finmap. intros i Hi.
  apply (Nat.lt_trans i n (S n)) in Hi. remember Hi as Hi'. clear HeqHi'.
  apply H in Hi. apply imc1 in Hi'. apply ind_cases in Hi.
  destruct Hi as [Hi|Hi]. assumption. contradiction.
  apply Nat.lt_succ_diag_r.
- right. assumption.
Qed.




Lemma contra_eqb_eq: forall a b : nat, (a =? b) = false -> a <> b.
Proof. induction a as [| a IHa]; induction b as [| b IHb]; intros; auto.
simpl in H. discriminate.
Qed.

Lemma contra_ltb_lt: forall a b : nat, (a <? b) = false -> a >= b.
Proof. intros. remember (Nat.lt_ge_cases a b) as abcases. clear Heqabcases.
destruct abcases as [abcase|abcase].
- apply Nat.ltb_lt in abcase. rewrite H in abcase. discriminate.
- assumption.
Qed.

Lemma erase_restr_lemma : forall f n m i, 
    finmap (S n) (S m) f -> inj (S n) f -> i < S n -> f i = m -> 
    finmap n m (erase f i) /\ inj n (erase f i).
Proof.
(** My proof does not use any induction, but lots of case analysis. **)
intros f n m i Hfin Hinj Hi Hfi. split.
- unfold finmap. intros i0 Hi0. 
  remember (Nat.lt_ge_cases i0 i) as icase. clear Heqicase.
  destruct icase as [icase|icase].
  + unfold erase. destruct (i0 <? i) eqn: icasebool.
    * remember (eq_neq i0 i) as Hi0i. clear HeqHi0i.
      destruct Hi0i as [Hi0i|Hi0i]. lia.
      unfold finmap in Hfin. apply (Nat.lt_trans i0 n (S n)) in Hi0.
      remember Hi0 as Hi0'. clear HeqHi0'.
      apply Hfin in Hi0. remember (ind_cases (f i0) m) as icase'. clear Heqicase'.
      apply icase' in Hi0. destruct Hi0 as [Hi0|Hi0].
      assumption. unfold inj in Hinj.
      assert (f i0 = f i) as Hfijeq. {rewrite Hi0. symmetry. assumption. }
      remember (Hinj i0 i Hi0' Hi Hfijeq) as Hij. clear HeqHij.
      contradiction. apply Nat.lt_succ_diag_r.
    * apply Nat.ltb_lt in icase. rewrite icase in icasebool. discriminate.
  + unfold erase. destruct (i0 <? i) eqn: icasebool.
    * apply Nat.ltb_lt in icasebool. lia.
    * clear icasebool. destruct ((S i0) =? i) eqn:HSi0.
      -- apply Nat.eqb_eq in HSi0. rewrite <- HSi0 in icase. lia.
      -- apply contra_eqb_eq in HSi0. unfold finmap in Hfin.
         apply Arith_prebase.lt_n_S_stt in Hi0.
         remember Hi0 as Hi0'. clear HeqHi0'. apply Hfin in Hi0.
         remember (ind_cases (f (S i0)) m) as HicSi0. clear HeqHicSi0.
         apply HicSi0 in Hi0. destruct Hi0 as [Hi0|Hi0].
         assumption. unfold inj in Hinj.
         assert (f (S i0) = f i) as HfSi0ieq. {rewrite Hi0. symmetry. assumption. }
         remember (Hinj (S i0) i Hi0' Hi HfSi0ieq) as HfSi0i.
         contradiction.
- unfold inj. intros j k Hj Hk. unfold erase.
  destruct (j <? i) eqn:jcase; destruct (k <? i) eqn:kcase; intros Hf;
  try apply Nat.ltb_lt in jcase; try apply Nat.ltb_lt in kcase;
  try apply contra_ltb_lt in jcase; try apply contra_ltb_lt in kcase;
  unfold inj in Hinj.
  + apply (Nat.lt_trans j n (S n)) in Hj. 
    apply (Nat.lt_trans k n (S n)) in Hk.
    apply (Hinj j k Hj Hk Hf). lia. lia.
  + apply Arith_prebase.lt_n_S_stt in Hk.
    apply (Nat.lt_trans j n (S n)) in Hj.
    remember (Hinj j (S k) Hj Hk Hf) as Heq. clear HeqHeq.
    lia. lia.
  + apply Arith_prebase.lt_n_S_stt in Hj.
    apply (Nat.lt_trans k n (S n)) in Hk.
    remember (Hinj (S j) k Hj Hk Hf) as Heq. clear HeqHeq.
    lia. lia.
  + apply Arith_prebase.lt_n_S_stt in Hj.
    apply Arith_prebase.lt_n_S_stt in Hk.
    remember (Hinj (S j) (S k) Hj Hk Hf) as Heq. clear HeqHeq.
    injection Heq as Heq. assumption.
Qed.


(* remember (range_lemma f n m) as rlem. clear Heqrlem.
    remember Hfin as Hfin2. clear HeqHfin2. 
    apply rlem in Hfin. destruct Hfin as [Hfin|Hfin].
    unfold finmap in Hfin. apply Hfin in Hi0. assumption.
    destruct Hfin as [w Hw]. destruct Hw as [Hw1 Hw2].
    unfold inj in Hinj. *)

Theorem php: forall n m f, finmap n m f -> m < n -> noninj n f.
Proof.
    intros n m f. rewrite <- inj_noninj. 
    generalize m f. clear f m. 
    induction n as [ | n IH]. 
    -   intros. inversion H0. 
    -   intros [ | m] f A Hlt Hinj. 
        apply A in Hlt. inversion Hlt.
        remember (range_lemma _ _ _ A) as B. clear HeqB. 
        destruct B as [B | [i [B C]]].
        *   apply inj_restr_lemma in Hinj. 
            apply IH in B. auto. lia.
        *   remember (erase_restr_lemma _ _ _ i A Hinj B C) as D.
            clear HeqD.
            destruct D as [D1 D2].
            apply IH in D1; auto. lia.
Qed.

