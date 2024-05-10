Require Import PHP.
Require Import Classes.
Require Import Lia.
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

	Lemma contrapositive_sig1 : forall P Q : Type, (P -> Q) -> ((Q -> False) -> (P -> False)).
	Proof. auto. Qed.

	Lemma contrapositive_sig2 : forall P Q : Type, ((Q -> False) -> (P -> False)) -> (P -> Q).
	Proof. intros P Q H Hp. destruct (lem_type Q); try assumption. apply H in f. contradiction. assumption.
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

	Definition injective {X Y : Type} (f : X -> Y) :=
		forall s t, f s = f t -> s = t.

	Definition increasing (qo : Quasi_Order R) (f : nat -> A) := forall x y : nat, x < y -> (f x) <=qo (f y).

	Definition antichain (qo : Quasi_Order R) (f : nat -> A) :=
  forall x y, x <> y -> ~((f x) <=qo (f y)) /\ ~((f y) <=qo (f x)).

	Definition strictly_descending (qo : Quasi_Order R) (f : nat -> A) :=
  forall x y, x < y -> ((f y) <=qo (f x)) /\ f x <> f y.

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

 

	Definition wqo_axiom2 (qo : Quasi_Order R) : Prop :=
	forall (f : nat -> A), exists (f' : nat -> nat),
	increasing Le_QO f' /\ increasing qo (fun n => f (f' n)).

	Definition wqo_axiom2_fn (qo : Quasi_Order R) (f : nat -> A) (f' : nat -> nat) : Prop := 
		increasing Le_QO f' /\ increasing qo (fun n => f (f' n)).

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
			~ (
				 (injective f /\ antichain qo f) \/
				 strictly_descending qo f).


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
	intros f.

