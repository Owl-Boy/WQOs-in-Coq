Require Import PHP.
Require Import Classes.
Require Import Lia.
Require Import Nat.
Require Import Bool.
Set Implicit Arguments.

Axiom lem_type : forall P : Type, (P) + (P -> False).
Axiom lem_sig : forall P : Prop,{P} + {~P}.

Lemma lem_pred : forall {A : Type}, forall P : A -> Prop,
	{a : A | P a} + ({a : A | P a} -> False).
Proof. intros A P. apply (lem_type {a : A | P a}).
Qed.

Lemma lem : forall P : Prop, P \/ ~P.
Proof. intros P. destruct (lem_sig P).
left. assumption. right. assumption.
Qed.

(* Lemma pred_lem_sig {A : Type} (w : A) : forall P : A -> Prop, {a : A | P a} + {a : A | ~ P a}.
Proof. intros P. destruct (lem_sig (P w)) as [H | H].
- left. apply exist with w. assumption.
- right. apply exist with w. assumption.
Qed. *)


Section Classical.

	Lemma dne : forall P : Prop, ~~P <-> P.
	Proof. split.
	- intros. unfold not in H. destruct (lem P); try assumption.
		apply H in H0. exfalso. assumption.
	- auto.
	Qed.

	Lemma dne_forall {A : Type} : forall P : A -> Prop,
		(forall a, ~~(P a)) <-> (forall a, P a).
	Proof. split.
	- intros. specialize H with a. 
		rewrite dne in H. assumption.
	- intros. apply dne. specialize H with a. assumption.
	Qed.

	Lemma nex_forall {A : Type} : forall (P : A -> Prop), ~(exists a, P a) <-> forall a, ~(P a).
	Proof. split.
	- eauto.
	- intros H. unfold not. intros H'.
		destruct H'. specialize H with x. contradiction.
	Qed.

	Lemma nforall_ex {A : Type} : forall (P : A -> Prop),
	~(forall a, P a) <-> exists a, ~(P a).
	Proof. split.
	- intros H. destruct (lem (exists a : A, ~ P a)); try assumption.
		rewrite nex_forall in H0. rewrite dne_forall in H0.
		contradiction.
	- intros H. unfold not. intros H'.
		destruct H. specialize H' with x. contradiction.
	Qed.

	Lemma nforall_ex_sig {A : Type} : 
	forall (P : A -> Prop),
	~(forall a, P a) -> {a : A | ~(P a)}.
	Proof. intros P H. unfold not in H.
	assert (({a : A | ~ P a} -> False) -> False).
	{ intros H'. apply H. intros a.
		destruct (lem_sig (P a)).
		- assumption.
		- exfalso. apply H'.
			apply exist with a. assumption.
	}
	destruct (lem_pred (fun a => ~ P a)).
	- assumption.
	- exfalso. apply H0. assumption.
	Qed.

	Lemma nforall_ex_sig_bin {A B : Type} :
	forall (P : A -> B -> Prop),
	~(forall a, forall b, P a b) -> {p : A * B | ~(P (fst p) (snd p))}.
	Proof. intros P Hp. apply nforall_ex_sig in Hp.
	destruct Hp as [a Ha].
	apply nforall_ex_sig in Ha.
	destruct Ha as [b Hab].
	apply exist with (a, b). auto.
	Qed.

	Lemma nforall_ex_type {A : Type} :
	forall (P : A -> Type),
	((forall a, P a) -> False) -> {a : A | (P a) -> False}.
	Proof. intros P H.
	assert (({a : A | (P a) -> False} -> False) -> False).
	{ intros H'. apply H. intros a.
		destruct (lem_type (P a)).
		- assumption.
		- exfalso. apply H'.
			apply exist with a. assumption.
	} 
	destruct (lem_pred (fun a => (P a) -> False)).
	- assumption.
	- exfalso. apply H0. assumption.
	Qed.



	Lemma imp_or : forall P Q : Prop, (P -> Q) <-> (~P \/ Q).
	Proof. split.
	- intros. destruct (lem P).
		right. apply H in H0. assumption.
		left. assumption.
	- tauto.
	Qed.

	Lemma imp_or_sig : forall P Q : Prop, (P -> Q) -> ({~P} + {Q}).
	Proof. intros. destruct (lem_sig P).
	right. apply H in p. assumption.
	left. assumption.
	Qed.

	Lemma imp_sum : forall P Q : Type, (P -> Q) -> ((P -> False) + Q).
	Proof. intros P Q H. destruct (lem_type P); destruct (lem_type Q); auto.
	Qed. 

	Lemma not_imp_and_sig : forall P Q : Type, ((P -> Q) -> False) -> (P * (Q -> False)).
	Proof. intros P Q H. destruct (lem_type P); destruct (lem_type Q); try auto.
	- assert (P -> Q) by auto. contradiction.
	- assert (P -> Q) by (intros; contradiction).
		contradiction.
	Qed.

	Lemma forall_or_counter_sig {A : Type} :
	forall (P : A -> Prop),
	(forall a, P a) + {a : A | ~(P a)}.
	Proof. intros P. specialize (nforall_ex_sig P); intros.
	destruct (lem_sig (forall a, P a)).
	- left; assumption.
	- right; auto.
	Qed.

	(* Lemma forall_or_counter_pred {A B : Type} :
	forall (P : A -> B -> Prop),
	(forall a, {b : B | P a b}) + {a : A | forall b, ~ P a b}. *)

	Lemma de_morgan_not_or : forall P Q : Prop, ~(P \/ Q) <-> (~P /\ ~Q).
	Proof. tauto. Qed.

	Lemma de_morgan_not_and : forall P Q : Prop, ~(P /\ Q) <-> (~P \/ ~Q).
	Proof. split; try tauto.
	intros. unfold not in H. destruct lem with P; destruct lem with Q; auto.
	Qed.


	Lemma pred_lem_sig {A B : Type} : forall P : A -> B -> Prop,
		{g : A -> B | forall a : A, P a (g a)} + {a : A | forall b : B, ~ (P a b)}.
	Proof. intros P.
	assert ((forall a : A, {b : B | P a b}) + {a : A | forall b : B, ~ (P a b)}).
	{ destruct (lem_pred (fun a => (forall b : B, ~ P a b))) as [H | H].
		- right. assumption.
		- left. intros a.
			destruct (lem_sig (forall b : B, ~ P a b)) as [Hb | Hb].
			+ exfalso. apply H. apply exist with a. assumption.
			+ apply nforall_ex_sig in Hb. destruct Hb.
				rewrite dne in n. apply exist with x.
				assumption.
	}
	destruct X as [H | H].
	- left. Check exist. apply exist with
			(fun a => match (H a) with
								| exist _ b _ => b
								end).
		intros a. destruct (H a). assumption.
	- right. assumption.
	Qed.

	Lemma ex_abs_forall_sig {A B : Type} :
		forall (P : A -> B -> Prop),
		({a : A | forall b : B, P a b} -> False)
		-> (forall a : A, {b : B | ~ P a b}).
	Proof. intros P H a. 
	destruct (lem_pred (fun b => (~ P a b))) as [Hb | Hb].
	- destruct Hb. apply exist with x. assumption.
	- exfalso. apply H. apply exist with a.
		intros b. destruct lem_sig with (P a b); try assumption.
		exfalso. apply Hb. apply exist with b. assumption.
	Qed.

	Lemma forall_abs_ex_sig {A : Type} :
		forall (P : A -> Type),
		((forall a : A, P a) -> False) -> {a : A | (P a) -> False}.
	Proof. intros P Hp.
	apply nforall_ex_type in Hp. assumption.
	Qed.

	Lemma contrapositive_sig1 : forall P Q : Type, (P -> Q) -> ((Q -> False) -> (P -> False)).
	Proof. auto. Qed.

	Lemma contrapositive_sig2 : forall P Q : Type, ((Q -> False) -> (P -> False)) -> (P -> Q).
	Proof. intros P Q H Hp. destruct (lem_type Q); try assumption. apply H in f. contradiction. assumption.
	Qed.

	Lemma de_morgan_or_sig : forall P Q : Type, ((P + Q) -> False) -> ((P -> False) * (Q -> False)).
	Proof. intros P Q HPQ.
	destruct (lem_type P); destruct (lem_type Q).
	Print sum.
	- assert (P + Q) by (exact (inl p)). auto.
	- assert (P + Q) by (exact (inl p)). auto.
	- assert (P + Q) by (exact (inr q)). auto.
	- exact (f, f0).
	Qed.

	Lemma de_morgan_and_sig : forall P Q : Type, ((P * Q) -> False) -> ((P -> False) + (Q -> False)).
	Proof. intros P Q HPQ.
	destruct (lem_type P); destruct (lem_type Q);
	try (right; assumption); try (left; assumption).
	- assert (P * Q) by (exact (pair p q)). auto.
	Qed.

End Classical.



(* Section Tests.

	Context {A : Type}.

	Check @to_comp.

	Example test : forall R : A -> A -> Prop, (Total_Order R) -> Completeness R.
	Proof. intros R H. apply (@to_comp A R). assumption. *)

Section Definitions.

	Context {A : Type}.
	Definition relation := A -> A -> Prop.

	Context {R : relation}.
	Notation "x <=qo y" := (R x y) (at level 50).


	Definition inj (f : nat -> nat) := forall x y, f x = f y -> x = y.

	Definition str_inc (f : nat -> nat) := forall n m,
		n < m -> f n < f m.

	Definition injective {X Y : Type} (f : X -> Y) :=
		forall s t, f s = f t -> s = t.

	Lemma str_inc_imp_inj : forall (f : nat -> nat),
		str_inc f -> injective f.
	Proof. intros f Hf.
	unfold str_inc in *; unfold injective in *.
	intros s t Hst. 
	assert (s = t \/ s > t \/ s < t) as [H | [H | H]] by lia; 
	try lia.
	- specialize Hf with t s. lia.
	- specialize Hf with s t. lia.
	Qed.

	Lemma inj_subseq_inj {Y : Type} : forall (f : nat -> Y),
		injective f -> forall (f' : nat -> nat),
		str_inc f' -> injective (fun n => f (f' n)).
	Proof. intros f Hf f' Hf'. unfold injective in *.
	intros s t. specialize (Hf (f' s) (f' t)).
	apply str_inc_imp_inj in Hf'. unfold injective in *.
	specialize Hf' with s t. auto.
	Qed.

	Definition increasing (qo : Quasi_Order R) (f : nat -> A) := forall x y : nat, x < y -> (f x) <=qo (f y).

	Definition antichain (qo : Quasi_Order R) (f : nat -> A) :=
  forall x y, x <> y -> ~((f x) <=qo (f y)) /\ ~((f y) <=qo (f x)).

	Definition strictly_descending (qo : Quasi_Order R) (f : nat -> A) :=
  forall x y, x < y -> ((f y) <=qo (f x)) /\ ~(f x <=qo f y).

	Definition comparable (qo : Quasi_Order R) (x y : A) :=
	(x <=qo y) \/ (y <=qo x).

	Definition dominated_by (qo : Quasi_Order R) (n m : nat) (f : nat -> A) : Prop := n < m /\ (f n) <=qo (f m).

	Definition dominators (qo : Quasi_Order R) (n : nat) (f : nat -> A) :=
		{m : nat | dominated_by qo m n f}.

	Lemma fin_or_inf_sig : forall P : nat -> Prop,
		{g : nat -> nat | forall n : nat, n < (g n) /\ ~(P (g n))} + {N : nat | forall n : nat, N < n -> P n}.
	Proof. intros P. Check pred_lem_sig.
	specialize (pred_lem_sig (fun n m : nat => n < m /\ ~ P m)); intros. simpl in *.
	destruct H as [H | H].
	- left. assumption.
	- right. destruct H as [a Ha].
		apply exist with a. intros n. specialize Ha with n.
		apply imp_or. rewrite de_morgan_not_and in Ha.
		destruct Ha; auto.
		rewrite dne in H; auto.
	Qed.


	Lemma fin_or_inf : forall P : nat -> Prop, 
		(forall N, exists n, N < n /\ ~ P n) \/ (exists N, forall n, N < n -> P n).
	Proof. intros P. destruct (lem (exists N : nat, forall n : nat, N < n -> P n)).
	- right. assumption.
	- left. intros N. apply (nex_forall (fun N => forall n : nat, N < n -> P n)) with N in H.
		rewrite nforall_ex in H.
		destruct H. exists x.
		rewrite imp_or in H. rewrite de_morgan_not_or in H.
		destruct H. rewrite dne in H.
		split; assumption.
	Qed.

End Definitions.

(* Lemma id_increasing : increasing Le_QO (fun n => n).
Proof. unfold increasing. lia. Qed. *)

(* Lemma test : forall x, exists y, y = x + 2. eauto. Qed.
Lemma test_sig : (forall x, {y | y = x + 2}) -> {f : nat -> nat | forall x, (f x) = x + 2}.
Proof. intros H.
Check exist.
apply exist with 
	(fun n => match (H n) with
						| exist _ x pf => x
						end).
intros x. destruct (H x). auto.
Qed. *)

Definition extract_fn_un {A B : Type} (P : A -> B -> Prop) :
	(forall a, {b | P a b}) -> {f : A -> B | forall a, P a (f a)}.
	intros H.
	apply exist with (fun a => match (H a) with
														 | exist _ b pf => b
														 end).
	intros. destruct (H a). assumption.
Qed.


Check (extract_fn_un (fun x y => y = x + 2)).
Lemma testing : {f | forall a, (f a) = a + 2}.
Proof. apply (extract_fn_un (fun x y : nat => y = x + 2)).
intros a. apply exist with (a + 2). reflexivity.
Qed.


Definition extract_fn_bin {A B C : Type} (P : A -> B -> C -> Prop) :
	(forall a, {p : B * C | P a (fst p) (snd p) }) -> {f : A -> B * C | forall a, P a (fst (f a)) (snd (f a))}.
	intros H.
	apply exist with (fun a => match (H a) with
														 | exist _ p pf => p
														 end).
	intros. destruct (H a). assumption.
Qed.



Lemma helper1_equiv1 {A B : Type} (P : A -> B -> Prop) :
	(forall (phi : A -> B), {a : A | P a (phi a)}) ->
	{a' : A | forall b : B, P a' b}.
Proof. (* we prove the contrapositive. *)
assert ((forall a', {b : B | ~ P a' b}) ->
	{phi : A -> B | forall a : A, ~ (P a (phi a))}).
{ intros H. apply exist with (fun a =>
	match (H a) with
	| exist _ b _ => b
	end).
	intros a. unfold not. intros H'. 
	remember (H a) as Ha; clear HeqHa; clear H.
	destruct Ha as [b Hb]. contradiction.
}
(* we now convert the contrapositive into the required statement *)
apply contrapositive_sig2.
intros H1 H2. destruct (lem_type (forall a' : A, {b : B | ~ P a' b})) as [H3 | H3].
- apply X in H3. destruct H3 as [phi Hphi].
	specialize H2 with phi as [a Ha].
	specialize Hphi with a. contradiction.
- apply H3. intros a.
	Check forall_or_counter_sig.
	specialize (forall_or_counter_sig (fun b => P a b)); intros.
	destruct X0 as [H4 | H4].
	+ exfalso. apply H1. apply exist with a.
		intros b. specialize H4 with b. assumption.
	+ assumption.
Qed.




Section WQO_Axioms.

	Context {A : Type}.
	Context {R : @relation A}.
	Notation "x <=qo y" := (R x y) (at level 50).

	Lemma loc_inc_imp_inc : forall (f : nat -> nat), 
		(forall n : nat, (f n) < (f (S n))) -> 
		(forall n m : nat, (n < m) -> (f n) < (f m)).
	Proof. induction n as [| n IHn]; induction m as [| m IHm]; try lia; intros.
	- clear H0. assert (0 < m \/ m = 0) as [H' | H'] by lia.
		+ specialize H with m. lia.
		+ subst. apply H.
	- assert ((S n) < m \/ (S n) = m) as [C | C] by lia.
		+ specialize H with m. lia.
		+ subst. apply H.
	Qed.

	Definition wqo_axiom1 (qo : Quasi_Order R) : Prop :=
  forall (f : nat -> A), exists x y, x < y /\ (f x) <=qo (f y).

	Definition wqo_axiom1_fn (qo : Quasi_Order R) (f : nat -> A) (x y : nat) : Prop := x < y /\ (f x) <=qo (f y).

	Definition wqo_axiom1_sig (qo : Quasi_Order R) := {g : (nat -> A) -> nat * nat | forall f : (nat -> A), wqo_axiom1_fn qo f (fst (g f)) (snd (g f))}.

	Lemma wqo_helper1 : forall (qo : Quasi_Order R), (wqo_axiom1_sig qo) -> (wqo_axiom1 qo).
	Proof. intros qo. unfold wqo_axiom1_sig, wqo_axiom1. intros H.
	destruct H. intros f. specialize w with f.
	unfold wqo_axiom1_fn in w.
	exists (fst (x f)). exists (snd (x f)).
	auto.
	Qed.

	Definition wqo_axiom1_var (qo : Quasi_Order R) (f : nat -> A) := {p : nat * nat | fst p < snd p /\ f (fst p) <=qo f (snd p)}.

	Lemma wqo_axiom1_var_sig (qo : Quasi_Order R) :
	(forall f : nat -> A, wqo_axiom1_var qo f) ->
	wqo_axiom1_sig qo.
	Proof. intros wqo1_var. unfold wqo_axiom1_var in *.
	unfold wqo_axiom1_sig in *.
	unfold wqo_axiom1_fn in *.
	apply exist with (fun f =>
		match (wqo1_var f) with
		| exist _ p _ => p
		end
	).
	intros f. remember (wqo1_var f) as H.
	destruct H as [[x y] Hxy]; simpl.
	simpl in *. auto.
	Qed.


	Lemma noninj_imp_wqo_axiom1 (qo : Quasi_Order R) : forall f : nat -> A, ~ injective f -> wqo_axiom1_var qo f.
	Proof. intros f Hf. unfold injective in *.
	unfold wqo_axiom1_var in *.
	apply forall_abs_ex_sig in Hf.
	destruct Hf as [k Hk].
	apply nforall_ex_sig in Hk. destruct Hk as [l Hkl].
	apply not_imp_and_sig in Hkl as [H1 H2].
	destruct (lem_type (k < l)).
	- apply exist with (k, l); split; auto; simpl.
		rewrite H1. apply qo_refl.
	- assert (l < k) by lia.
		apply exist with (l, k); split; auto; simpl.
		rewrite H1. apply qo_refl.
	Qed.

	Definition wqo_axiom2 (qo : Quasi_Order R) : Prop :=
	forall (f : nat -> A), exists (f' : nat -> nat),
	str_inc f' /\ increasing qo (fun n => f (f' n)).

	Definition wqo_axiom2_fn (qo : Quasi_Order R) (f : nat -> A) (f' : nat -> nat) : Prop := 
		str_inc f' /\ increasing qo (fun n => f (f' n)).

	Definition wqo_axiom2_sig (qo : Quasi_Order R) := 
		{g : (nat -> A) -> (nat -> nat) | forall f : (nat -> A), wqo_axiom2_fn qo f (g f)}.

	Lemma wqo_helper2 : forall (qo : Quasi_Order R), (wqo_axiom2_sig qo) -> (wqo_axiom2 qo).
	Proof. intros qo. unfold wqo_axiom2_sig, wqo_axiom2. intros H.
	destruct H. intros f. specialize w with f.
	unfold wqo_axiom2_fn in w.
	exists (x f).
	auto.
	Qed.


	Definition wqo_axiom3 (qo : Quasi_Order R) : Prop :=
	forall f : nat -> A,
			(
				 (injective f * antichain qo f) +
				 strictly_descending qo f) -> False.

	Lemma wqo3_de_morgan : forall (qo : Quasi_Order R),
		wqo_axiom3 qo -> (forall f : nat -> A,
		((~injective f) + (~antichain qo f)) * 
		(~strictly_descending qo f)).
	Proof. intros qo wqo3. unfold wqo_axiom3 in *.
	intros f. specialize wqo3 with f.
	apply (de_morgan_or_sig) in wqo3 as [H1 H2].
	apply (de_morgan_and_sig) in H1.
	exact (H1, H2).
	Qed.


	Theorem wqo_equiv1 : forall (qo : Quasi_Order R),
	(wqo_axiom1_sig qo) -> (wqo_axiom2_sig qo).
	Proof. intros qo. unfold wqo_axiom1_sig, wqo_axiom2_sig. 
	intros S. destruct S as [g Hg].
	unfold wqo_axiom1_fn in Hg. unfold wqo_axiom2_fn.
	
	(* there is either m such that m dominates n, or the existence of such an m is absurd. *)
	
	assert (forall n, forall f, 
		{m : nat | dominated_by qo n m f} +
		({m : nat | dominated_by qo n m f} -> False)
	) as lp.
	{ intros n f. apply lem_pred. }
	
	(* there is either m such that m dominates n, or forall m, n is not dominated by m. *)
	
	assert (forall n, forall f,
		{m : nat | dominated_by qo n m f} +
		(forall m : nat, ~(dominated_by qo n m f))
	) as lp'.
	{ intros n f. specialize lp with n f.
		destruct lp as [lp | lp].
		- left; assumption.
		- right. intros m. unfold not; intros Hdom.
			apply lp. apply exist with m. assumption.
	}
	
	(* for every sequence in A, there exists N : nat such that for n > N, n is dominated. *)
	
	assert (forall f, 
		{p : nat * (nat -> nat) |
		let N := (fst p) in
		let g := (snd p) in
		forall m, N < m -> dominated_by qo m (g m) f}).
	{ simpl. Check pred_lem_sig.
		destruct (pred_lem_sig (fun (f : nat -> A) (p : nat * (nat -> nat)) => (forall m : nat, fst p < m -> dominated_by qo m (snd p m) f))) as [Hpls | Hpls].
		- destruct Hpls as [h Hh]. intros f.
			remember (Hh f) as Hhf; clear HeqHhf.
			apply exist with (h f). assumption.
		
		(* if not: there exists a sequence h such that for all N : nat, there is n > N such that n is NOT dominated in h *)
		- destruct Hpls as [h Hh].
			(* we assert that h is that sequence. *)
			assert (forall N : nat, {n : nat | N < n /\ forall m : nat, ~(dominated_by qo n m h)}).
			{ intros N. 
				assert (forall b : nat * (nat -> nat),
					{m : nat | fst b < m /\ ~ dominated_by qo m (snd b m) h}).
				{ intros b. specialize Hh with b. 
					apply nforall_ex_sig in Hh.
					destruct Hh as [a Ha]. apply exist with a.
					rewrite imp_or in Ha. 
					apply de_morgan_not_or in Ha. destruct Ha.
					rewrite dne in H. split; assumption.
				}
				clear Hh; remember H as Hh; clear HeqHh; clear H.
				assert (forall B : nat, forall phi : (nat -> nat),
					{m : nat | B < m /\ ~ dominated_by qo m (phi m) h}).
				{ intros B phi. specialize Hh with (B, phi).
					assumption.
				}
				clear Hh; remember H as Hh; clear HeqHh; clear H.
				remember (Hh N) as HhN; clear HeqHhN; clear Hh.
				Check helper1_equiv1.
				assert ({n : nat | forall m : nat, N < n /\ ~ dominated_by qo n m h}).
				{ apply (helper1_equiv1 (fun (n m : nat) =>
					(N < n /\ ~ dominated_by qo n m h))).
					assumption.
				}
				destruct H as [n Hn].
				exists n; split.
				- specialize Hn with 0 as [Hn _]. assumption.
				- intros m. specialize Hn with m as [_ Hn].
					assumption.
			}
			
			(* therefore, there exists a subsequence f' of h such that no element is dominated. this will be denoted phi in the sequel. *)
			
			remember (fix phi (k : nat) :=
					match k with
					| 0 => match (H 0) with
								 | exist _ n _ => n
								 end
					| S k' => match (H (phi k')) with
								 | exist _ n _ => n
								 end
					end
				) as phi.
			
			(* lemma: phi is locally increasing. *)
			assert (forall n : nat, phi n < phi (S n))
								as phi_loc_inc.
			{ simpl. intros n. subst.
				destruct (H
     			((fix phi (k : nat) : nat :=
        			match k with
        			| 0 => let (n0, _) := H 0 in n0
        			| S k' => let (n0, _) := H (phi k') in n0
        			end) n)
					) as [n' Hn'].
				destruct (H n') as [n'' Hn'']; lia.
			}
			(* lemma: phi is increasing. *)
			assert (forall n m : nat, n < m -> phi n < phi m)
			as phi_inc.
			{ apply (loc_inc_imp_inc phi phi_loc_inc). }
			clear phi_loc_inc.
			
			(* we now assert that phi is the bad subsequence of h. *)
			assert ({f' : nat -> nat | forall n m : nat,
				~ dominated_by qo n m (fun n' => h (f' n'))})
			as nondom_seq.
			{ apply exist with phi.
				unfold dominated_by.
				assert (forall n : nat, forall m : nat, ~ dominated_by qo (phi n) m h).
				{ induction n as [| n IHn].
					- destruct (H 0). subst. tauto.
					- intros m. 
						destruct (H (phi n)) as [pn [Hpn1 Hpn2]] eqn:Epn.
						rewrite Heqphi. rewrite <- Heqphi. 
						rewrite Epn. apply Hpn2.
				}
				unfold dominated_by in H0. intros n m.
				specialize H0 with n (phi m). unfold not in H0.
				unfold not. intros [Hc1 Hc2].
				specialize (phi_inc) with n m.
				apply phi_inc in Hc1. auto.
			}
			
			(* once we have the bad subsequence, we just need to derive a contradiction using the wqo axiom 1 hypothesis. *)
			(* in particular, g is the function that takes in a sequence in the partial order and outputs n, m such that n is dominated by m in the given sequence. g's output on the input (n => h (phi n)) must therefore be absurd. *)
			
			exfalso; clear lp lp'.
			destruct nondom_seq as [fnd Hfnd].
			specialize Hg with (fun n => h (fnd n)).
			destruct (g (fun n => h (fnd n))) as [p1 p2].
			simpl in *. unfold dominated_by in Hfnd.
			specialize Hfnd with p1 p2. auto.
	}
	
	(* therefore, we have shown that for every sequence
		 nat -> A, there is N : nat such that beyond n, every 		 element is dominated by something. this lets us
		 extract the infinitely increasing subsequence. *)
	clear lp lp' Hg. Print increasing. Print exist.
	remember (fix g0 (f : nat -> A) (n : nat) :=
		match (X f) with
		| exist _ (N, phi) _ =>
			match n with
			| 0 => phi (N + 1)
			| S n => phi (g0 f n)
			end
		end
	) as Psi.
	apply exist with Psi.
	intros f.
	
	(* lemma: (Psi f) and f (Psi f) are locally increasing. *)
	assert (forall n : nat, (Psi f n) < (Psi f (S n)) /\
		f (Psi f n) <=qo f (Psi f (S n)))
	as Psif_loc_inc_with_f.
	{ intros n. induction n as [| n IHn].
		- subst. destruct (X f) as [[N phi] Hp]. simpl in *.
			remember (Hp (N + 1)) as HpSN; clear HeqHpSN.
			specialize Hp with (phi (N + 1)).
			assert (N < N + 1) by lia. apply HpSN in H.
			unfold dominated_by in H. destruct H as [H _].
			assert (N < phi (N + 1)) by lia.
			apply Hp in H0. unfold dominated_by in H0. tauto.
		- rewrite HeqPsi. destruct (X f) as [[N phi] Hp] eqn:EXf.
			simpl in *. 
			remember (Hp (phi (Psi f n))) as HpPfn; clear HeqHpPfn.
			rewrite <- HeqPsi.
			(* lemma: (Psi f 0) > N *)
			assert (N < Psi f 0) as HPf0.
			{ rewrite HeqPsi. rewrite EXf.
				remember (Hp (N + 1)) as HpSN; clear HeqHpSN.
				assert (N < N + 1) by lia.
				apply HpSN in H. unfold dominated_by in H.
				lia.
			}
			assert (Psi f 0 = (phi (N + 1))) as HPsiphi.
			{ rewrite HeqPsi. rewrite EXf. reflexivity. }
			(* lemma: (Psi f 0) < (Psi f n) for all n. *)
			assert (forall m : nat, 0 < m -> Psi f 0 < Psi f m)
			as Hpf0n.
			{ intros m Hm. induction m as [| m IHm]; try lia.
				rewrite HeqPsi. simpl. rewrite EXf. 
				rewrite <- HeqPsi.
				clear Hm. destruct m as [| m].
				- rewrite HeqPsi. rewrite EXf. clear IHm.
					rewrite HPsiphi in HPf0.
					remember (Hp (phi (N + 1))) as HpphiSN.
					apply HpphiSN in HPf0.
					unfold dominated_by in HPf0. destruct HPf0 as [HPf0 _]. auto.
				- assert (0 < S m) by lia. apply IHm in H. 
					clear IHm.
					remember (Hp (Psi f (S m))) as HpPfSm;
					clear HeqHpPfSm.
					assert (N < Psi f (S m)) by lia.
					apply HpPfSm in H0. unfold dominated_by in H0.
					destruct H0 as [H0 _]. lia.
			}
			specialize Hpf0n with (S n).
			rewrite HeqPsi in Hpf0n. rewrite EXf in Hpf0n.
			rewrite <- HeqPsi in Hpf0n. simpl in *.
			assert (phi (N + 1) < phi (Psi f n)) by lia; 
			clear Hpf0n. rewrite HPsiphi in HPf0.
			assert (N < phi (Psi f n)) by lia.
			apply HpPfn in H0. unfold dominated_by in H0.
			destruct H0 as [H00 H01]. auto.
	}
	(* lemma: Psi f alone is locally increasing. *)
	assert (forall n : nat, Psi f n < Psi f (S n))
	as Psif_loc_inc.
	{ intros n. specialize Psif_loc_inc_with_f with n.
		tauto.
	}
	(* lemma: Psi f is increasing. *)
	assert (forall n m : nat, n < m -> Psi f n < Psi f m)
	as Psif_inc.
	{ apply (loc_inc_imp_inc (Psi f) Psif_loc_inc). }
	split.
	- unfold increasing. intros x y Hxy. 
		specialize Psif_inc with x y. lia.
	- unfold increasing.
		induction x as [| x IHx]; induction y as [| y IHy];
		try lia.
		+ intros Hy. clear Hy.
			assert (0 < y \/ y = 0) as [H' | H'] by lia.
			* apply IHy in H'.
				specialize Psif_loc_inc_with_f with y.
				destruct Psif_loc_inc_with_f as [_ H''].
				apply (qo_trans (f (Psi f 0)) (f (Psi f y)) (f (Psi f (S y)))); auto.
			* subst y. clear IHy.
				specialize Psif_loc_inc_with_f with 0 as [_ H].
				auto.
		+ intros Hxy. 
			assert (S x < y \/ (S x) = y) as [H | H] by lia.
			* apply IHy in H.
				specialize (Psif_loc_inc_with_f) with y as [_ H'].
				apply (qo_trans (f (Psi f (S x))) (f (Psi f y)) (f (Psi f (S y)))); auto.
			* subst y. 
				specialize Psif_loc_inc_with_f with (S x) as [_ H].
				auto.
	Qed.



	Theorem wqo_equiv2 : forall (qo : Quasi_Order R),
	(wqo_axiom2_sig qo) -> wqo_axiom3 qo.
	Proof.
	intros qo Hwqo2. unfold wqo_axiom3.
	unfold wqo_axiom2_sig in *.
	intros f. unfold not. intros.
	destruct Hwqo2 as [g Hg].
	unfold wqo_axiom2_fn in Hg.
	specialize Hg with f.
	destruct Hg as [Hg1 Hg2].
	destruct H as [[H1 H2] | H].
	- unfold increasing in *.
		unfold str_inc in *.
		specialize Hg2 with 0 1.
		assert (0 < 1) as Hg2' by lia; apply Hg2 in Hg2'.
		clear Hg2.
		unfold antichain in *. unfold injective in *.
		specialize Hg1 with 0 1. 
		assert (g f 0 <> g f 1) by lia.
		specialize H2 with (g f 0) (g f 1). tauto.
	- unfold strictly_descending in *.
		unfold increasing in *.
		unfold str_inc in *.
		specialize Hg1 with 0 1.
		specialize Hg2 with 0 1.
		specialize H with (g f 0) (g f 1).
		assert ((g f 0) < (g f 1)) by lia.
		apply H in H0. assert (0 < 1) by lia.
		apply Hg2 in H1. destruct H0 as [_ H0].
		contradiction.
	Qed.



	Theorem wqo_equiv3 : forall (qo : Quasi_Order R),
		wqo_axiom3 qo -> forall f, wqo_axiom1_var qo f .
	Proof.
	intros qo. 
	unfold wqo_axiom3 in *. unfold wqo_axiom1_var.
	intros wqo3 f.
	(* we want to assume ~wqo_axiom1_sig qo FTSOC. *)
	destruct (lem_type (wqo_axiom1_var qo f)) as [H | not_wqo1]; auto.
	(* we now have the assumption to the contrary. *)
	unfold wqo_axiom1_sig.
	remember (wqo3_de_morgan wqo3) as wqo3';
	clear Heqwqo3';
	clear wqo3; rename wqo3' into wqo3.
	
	(* lemma: forall f, if f is injective, then it is not an antichain. *)
	assert (forall f : nat -> A, injective f -> ~(antichain qo f)) as inj_non_ac.
	{ intros f0. specialize wqo3 with f0 as [[H1 | H2] H3];
		auto.
	}
	(* lemma: for all injective f : nat -> A, there is a point N, beyond which every element n has a further element m such that (f m) <qo (f n). *)
	(* the upshot being that we will keep using this lemma to build an infinite strictly decreasing sequence. *)
	remember (fun (f : nat -> A) =>
			injective f ->
				{p : nat * (nat -> nat) | (let N := fst p in let g := snd p in
				forall n : nat, ( N < n -> (n < (g n) /\
				((f (g n)) <=qo (f n)) /\ ~((f n) <=qo (f (g n)))
	)))}) as lemprop.
	assert ((forall f : nat -> A, (lemprop f) + ((lemprop f -> False)))) as Hlem.
	{ intros f'. destruct (lem_type (lemprop f')); auto.
	}
	rename Hlem into Hlempre.
	(* assert that it is safe to assume that f is injective. *)
	assert (injective f) as Hfinj.
	{ unfold wqo_axiom1_var in not_wqo1.
		destruct (lem_type (injective f)) as [H | H]; auto.
		remember (noninj_imp_wqo_axiom1 qo H) as Hninj; clear HeqHninj.
		unfold wqo_axiom1_var in Hninj. contradiction.
	}
	destruct (Hlempre f) as [Hlem | Hlem].
	(* case: the lemma is true for f. we now need to prove falsehood assuming the lemma. *)
	- subst lemprop. clear Hlempre.
		remember (fix g0 (injpf : injective f) (k : nat) :=
			match (Hlem injpf) with
			| exist _ (N, g) _ =>
				match k with
				| 0 => N + 1
				| S k => g (g0 injpf k)
				end
			end
		) as Psi.
		(* now show that we can assume that f is injective. *)
		(* lemma: Psi is (locally) strictly increasing and f (Psi) is (locally) strictly descending. *)
		assert (forall n : nat,
			( (Psi Hfinj n) < (Psi Hfinj (S n)) /\
				( (f (Psi Hfinj (S n)) <=qo (f (Psi Hfinj n)) /\
				 	~((f (Psi Hfinj n)) <=qo (f (Psi Hfinj (S n))))
				) )
			) )
		as Psif_loc.
		{ intros n. simpl.
			induction n as [| n IHn].
			(* n = 0 *)
			+ destruct (Hlem Hfinj) as [(N, g) Hp] eqn:EHlem.
				rewrite HeqPsi. rewrite EHlem. simpl in *.
				split; try split; remember (Hp (N + 1)) as H;
				destruct H as [H1 [H2 H3]]; try assumption; try lia.
			(* S n *)
			+ destruct (Hlem Hfinj) as [(N, g) Hp] eqn:EHlem.
				rewrite HeqPsi. rewrite EHlem. simpl in *.
				rewrite <- HeqPsi.
				(* lemma: (g Psif n) > N forall n. *)
				assert (forall n : nat, N < (g (Psi Hfinj n))) as gnbig.
				{ intros m. induction m as [| m IHm].
					- rewrite HeqPsi. rewrite EHlem.
						remember (Hp (N + 1)). lia.
					- rewrite HeqPsi. rewrite EHlem. simpl in *.
						rewrite <- HeqPsi.
						remember (Hp (g (Psi Hfinj m))). lia.
				}
				remember (Hp (g (Psi Hfinj n))) as H.
				specialize gnbig with n. apply H in gnbig.
				clear HeqH. clear H. rename gnbig into H.
				tauto.
		}
		(* lemma: Psif is strictly increasing and f (Psif) is strictly decreasing. *)
		assert (forall n m : nat, n < m -> let Psif := (Psi Hfinj) in
			( (Psif n) < (Psif m) /\ ((f (Psif m)) <=qo (f (Psif n)) /\ ~ ((f (Psif n)) <=qo (f (Psif m)))))) as Psif_glob.
		{
			induction n as [| n IHn]; induction m as [| m IHm];
			try lia.
			- intros H; clear H. simpl.
				assert (0 < m \/ m = 0) as [H | H] by lia.
				+ apply IHm in H. simpl in *.
					repeat (try split); 
					specialize Psif_loc with m;
					destruct Psif_loc as [P1 [P2 P3]];
					destruct H as [H1 [H2 H3]].
					* lia.
					* apply (qo_trans
							(f (Psi Hfinj (S m)))
							(f (Psi Hfinj m))
							(f (Psi Hfinj 0))
						); auto.
					* unfold not. intros Hcon.
						assert (f (Psi Hfinj m) <=qo f (Psi Hfinj (S m))).
						{ apply (qo_trans
								(f (Psi Hfinj m))
								(f (Psi Hfinj 0))
								(f (Psi Hfinj (S m)))
							); auto.
						}
						auto.
				+ subst m. specialize Psif_loc with 0. auto.
			- intros Hnm. simpl in *.
				assert (S n < m \/ (S n = m)) as [Hc | Hc] by lia.
				+ apply IHm in Hc as [Hc1 [Hc2 Hc3]].
					specialize Psif_loc with m.
					destruct Psif_loc as [P1 [P2 P3]].
					repeat (try split).
					* lia.
					* apply (qo_trans
							(f (Psi Hfinj (S m)))
							(f (Psi Hfinj m))
							(f (Psi Hfinj (S n)))
						); auto.
					* unfold not. intros Hcon.
						assert (f (Psi Hfinj m) <=qo f (Psi Hfinj (S m))).
						{ apply (qo_trans
								(f (Psi Hfinj m))
								(f (Psi Hfinj (S n)))
								(f (Psi Hfinj (S m)))
							); auto.
						}
						auto.
				+ subst m. specialize Psif_loc with (S n).
					auto.
		}
		clear Psif_loc.
		(* write that f (Psif) is strictly decreasing in the correct form: *)
		assert (
			strictly_descending qo (fun n => f (Psi Hfinj n))).
		{ unfold strictly_descending.
			intros x y Hxy.
			specialize Psif_glob with x y.
			apply Psif_glob in Hxy. tauto.
		}
		(* finally, assert that there is an infinite strictly decreasing sequence. we use the function i created at the beginning for this. *)
		remember (wqo3 (fun n : nat => f (Psi Hfinj n))) 
		as wqo3Psii. 
		destruct wqo3Psii as [unused wqo3i].
		contradiction.
	
	(* case: the lemma that there is a bound beyond which ...
		 is false. We need to prove absurdity here again. *)
	- subst lemprop. clear Hlempre.
		remember (injective f) as P; remember (
			{p : nat * (nat -> nat)
      | let N := fst p in
        let g := snd p in
        forall n : nat,
        N < n ->
        n < g n /\ f (g n) <=qo f n /\ ~ f n <=qo f (g n)}
			) as Q.
		assert (P /\ (Q -> False)).
		{ destruct (lem_type P); destruct (lem_type Q); auto.
		}
		rename H into Hf. subst P; subst Q.
		destruct Hf as [Hfinj' Hfseq].
		assert (forall N : nat, forall g : (nat -> nat),
			{n : nat | N < n /\
			((g n <= n) \/ ~ (f (g n) <=qo f n) \/ (f n <=qo f (g n)))}).
		{ intros N g.
			destruct (lem_type (forall n : nat, N < n -> 
				(n < g n /\ f (g n) <=qo f n /\ ~ f n <=qo f (g n))
			)) as [H | H].
			- assert ({p : nat * (nat -> nat)
        | let N := fst p in
          let g := snd p in
          forall n : nat,
          N < n ->
          n < g n /\ f (g n) <=qo f n /\ ~ f n <=qo f (g n)}
				).
				{ apply exist with (N, g); auto. }
				contradiction.
			- apply forall_abs_ex_sig in H.
				destruct H as [n Hn]. apply exist with n.
				apply not_imp_and_sig in Hn as [Hn1 Hn2].
				apply de_morgan_not_and in Hn2 as [Hn2 | Hn3].
				+ split; auto; try lia.
				+ split; auto. apply de_morgan_not_and in Hn3.
					right. rewrite dne in Hn3. auto.
		}
		clear Hfseq. rename H into Hfseq.
		assert (forall N : nat, {n : nat | forall m : nat,
			N < n /\ (m <= n \/ ~ f m <=qo f n \/ f n <=qo f m)}).
		{ intros N. remember (Hfseq N) as HN; clear HeqHN. Check helper1_equiv1.
			apply (helper1_equiv1 (fun (n m : nat) =>
				(N < n /\ 
				(m <= n \/ ~ f m <=qo f n \/ f n <=qo f m) 
			)))in HN.
			destruct HN as [n Hn]. apply exist with n. auto.
		}
		clear Hfseq. rename H into Hfseq.
		
		unfold wqo_axiom1_var in not_wqo1.
		destruct (wqo3 f) as [wqo3f1 wqo3f2].
		
		assert (forall N : nat,
			{n : nat | N < n /\ forall m : nat,
			(n < m -> ~ comparable qo (f n) (f m))}).
		{	intros N.
			specialize Hfseq with N.
			destruct Hfseq as [n Hn].
			apply exist with n; split.
			- specialize Hn with 0; tauto.
			- intros m. specialize Hn with m.
				intros Hnm. 
				destruct Hn as [Hn1 [Hn2 | [Hn2 | Hn2]]].
				+ lia.
				+ unfold not. unfold comparable. intros [H | H].
					* assert ({p : nat * nat
           	| fst p < snd p /\ f (fst p) <=qo f (snd p)}).
						{ apply exist with (n, m); simpl; tauto. }
						contradiction.
					* contradiction.
				+ assert ({p : nat * nat
           	| fst p < snd p /\ f (fst p) <=qo f (snd p)}).
						{ apply exist with (n, m); simpl; tauto. }
						contradiction.
		}
		clear Hfseq. rename H into Hfseq.
		
		(* need to make an infinite antichain now. *)
		(* do this by using Hfseq to build up as usual. *)
		
		remember (fix phi (k : nat) :=
			match k with
			| 0 => match (Hfseq 0) with
						 | exist _ n _ => n
						 end
			| S k => match (Hfseq (phi k)) with
							 | exist _ n _ => n
							 end
			end
		) as phi.
		(* phi is our required function. *)
		
		(* lemma: phi is locally increasing (and therefore increasing) *)
		assert (forall n : nat, phi n < phi (S n)) as loc_inc_phi.
		{ induction n as [| n IHn].
			- destruct (Hfseq 0) eqn:Efseq.
				rewrite Heqphi. destruct (Hfseq x) eqn:Efseqx.
				clear Efseqx. tauto.
			- rewrite Heqphi. simpl. rewrite <- Heqphi.
				destruct (Hfseq (phi n)) eqn:Efseq.
				destruct (Hfseq x).
				tauto.
		}
		assert (forall n m : nat, n < m -> phi n < phi m)
		as str_inc_phi
		by exact (loc_inc_imp_inc phi loc_inc_phi).
		clear loc_inc_phi.
		
		(* lemma: f (phi) is an antichain *)
		assert (antichain qo (fun n => f (phi n)))
		as phi_ac.
		{ unfold antichain.
			induction x as [| x IHx]; induction y as [| y IHy];
			try lia.
			- clear IHy.
				intros H; clear H.
				rewrite Heqphi. simpl. rewrite <- Heqphi.
				destruct (Hfseq 0) as [n0 Hn0] eqn:Efseq0.
				destruct (Hfseq (phi y)) as [npy Hnpy] eqn:Efseqy.
				assert (n0 = phi 0).
				{ rewrite Heqphi. reflexivity. }
				assert (n0 < npy).
				{ rewrite H. specialize str_inc_phi with 0 y.
					destruct y as [| y].
					- destruct Hnpy as [Hnpy HH]. auto.
					- lia.
				}
				destruct Hn0 as [Hunused Hn0].
				remember (Hn0 npy). apply n in H0.
				unfold comparable in H0. auto.
			- intros H; clear H.
				rewrite Heqphi. simpl. rewrite <- Heqphi.
				destruct (Hfseq 0) as [n0 Hn0] eqn:Efseq0.
				destruct (Hfseq (phi x)) as [npx Hnpx] eqn:Efseqx.
				assert (n0 = phi 0).
				{ rewrite Heqphi. reflexivity. }
				assert (n0 < npx).
				{ rewrite H. specialize str_inc_phi with 0 x.
					destruct x as [| x].
					- destruct Hnpx as [Hnpx HH]. auto.
					- lia.
				}
				destruct Hn0 as [Hunused Hn0].
				remember (Hn0 npx). apply n in H0.
				unfold comparable in H0. auto.
			- intros Hxy. clear IHy.
				rewrite Heqphi. simpl. rewrite <- Heqphi.
				destruct (Hfseq (phi x)) as [npx Hnpx] eqn:Efseqx.
				destruct (Hfseq (phi y)) as [npy Hnpy] eqn:Efseqy.
				(* rewrite Heqphi in IHx. simpl in IHx.
				rewrite <- Heqphi in IHx. *)
				assert (npx = phi (S x)) as Hpnpx.
				{ rewrite Heqphi. rewrite <- Heqphi.
					rewrite Efseqx. reflexivity.
				}
				assert (npy = phi (S y)) as Hpnpy.
				{ rewrite Heqphi. rewrite <- Heqphi.
					rewrite Efseqy. reflexivity.
				}
				assert (npx <> npy) as npx_neq_npy.
				{ rewrite Hpnpx. rewrite Hpnpy.
					assert (S x < S y \/ S y < S x) as [H | H]
					by lia.
					- specialize str_inc_phi with (S x) (S y).
						lia.
					- specialize str_inc_phi with (S y) (S x).
						lia.
				}
				assert (npx < npy \/ npy < npx) as [H | H] by lia.
				+ destruct Hnpx as [Hun Hnpx]. 
					remember (Hnpx (npy)). apply n in H.
					unfold comparable in H. auto.
				+ destruct Hnpy as [Hun Hnpy].
					remember (Hnpy (npx)). apply n in H.
					unfold comparable in H. auto.
		}
		(* we now assert that the function g = f (phi) is injective. *)
		remember (fun n : nat => f (phi n)) as g.
		assert (injective g) as g_inj.
		{ rewrite Heqg. 
			apply (inj_subseq_inj Hfinj str_inc_phi).
		}
		specialize wqo3 with g. destruct wqo3 as [wqo3 _].
		destruct wqo3 as [wqo3 | wqo3]; contradiction.
	Qed.




	Theorem wqo_equiv (qo : Quasi_Order R) :
	(wqo_axiom1_sig qo -> wqo_axiom2_sig qo) *
	(wqo_axiom2_sig qo -> wqo_axiom3 qo) *
	(wqo_axiom3 qo -> wqo_axiom1_sig qo)
	.
	Proof. repeat split.
	- apply wqo_equiv1.
	- apply wqo_equiv2.
	- intros wqo3.
		apply wqo_axiom1_var_sig. apply wqo_equiv3.
		assumption.
	Qed.



