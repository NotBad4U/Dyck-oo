(** * The logic of subintervals [ITL_n] (§ 3, "The logic of subintervals") *)

From Stdlib Require Import Arith Lia.
Import Nat.
From Dyck Require Import Interval.

Declare Scope itl_scope.
Delimit Scope itl_scope with itl.
Open Scope itl_scope.

Section Syntax.

(** The formulas of the language *)
Inductive form : Set :=
| FBot
| FTop
| FVar (i : nat) (* propositional variable [ε_i], written [ε i] *)
| FOr (φ ψ : form)
| FAnd (φ ψ : form)
| FImp (φ ψ : form)
| FNeg (φ : form)
| FBox (φ : form)
| FDia (φ : form)
| FPNeg (φ : form)
| FPImp (φ ψ : form).

End Syntax.

Bind Scope itl_scope with form.

Notation "⊥" := FBot : itl_scope.
Notation "⊤" := FTop : itl_scope.
Notation "'ε' i" := (FVar i) (at level 10, i at level 9) : itl_scope.
Notation "φ ∨ ψ" := (FOr φ ψ) (at level 50, left associativity) : itl_scope.
Notation "φ ∧ ψ" := (FAnd φ ψ) (at level 40, left associativity) : itl_scope.
Notation "φ → ψ" := (FImp φ ψ) (at level 60, right associativity) : itl_scope.
Notation "¬ φ" := (FNeg φ) (at level 35, right associativity) : itl_scope.
Notation "□ φ" := (FBox φ) (at level 35, right associativity) : itl_scope.
Notation "◇ φ" := (FDia φ) (at level 35, right associativity) : itl_scope.
Notation "∼ φ" := (FPNeg φ) (at level 35, right associativity) : itl_scope.
Notation "φ ⇝ ψ" := (FPImp φ ψ) (at level 60, right associativity) : itl_scope.

(** [vars_in n φ]: the variables of [φ] are among [ε_1, …, ε_n], i.e. [φ ∈ ITL_n]. *)
Fixpoint vars_in n (φ : form) : Prop :=
  match φ with
  | ⊥ | ⊤ => True
  | ε i => 1 <= i <= n
  | φ ∨ ψ | φ ∧ ψ | φ → ψ | φ ⇝ ψ => vars_in n φ /\ vars_in n ψ
  | ¬ φ | □ φ | ◇ φ | ∼ φ => vars_in n φ
  end.

Section Semantics.

(** [val φ I]: [φ] is true on the interval [I].
  In particular [ε_i] is true if and only if I = [[t_i, t_i]] = {t_i}.
*)
Fixpoint val (φ : form) (I : interval) : Prop :=
  match φ with
  | ⊥ => False
  | ⊤ => True
  | ε i => I = Itv i i (* = {t_i} *)
  | φ ∨ ψ => val φ I \/ val ψ I
  | φ ∧ ψ => val φ I /\ val ψ I
  | φ → ψ => val φ I -> val ψ I
  | ¬ φ => ~ val φ I
  | □ φ => forall J, J ⊆ I -> val φ J
  | ◇ φ => exists J, J ⊆ I /\ val φ J
  | ∼ φ => forall J, J ⊆ I -> ~ val φ J
  | φ ⇝ ψ => forall J, J ⊆ I -> val φ J -> val ψ J
  end.

Lemma val_dec φ I : {val φ I} + {~ val φ I}.
Proof.
  revert I; induction φ as [| |i|φ IHφ ψ IHψ|φ IHφ ψ IHψ|φ IHφ ψ IHψ|φ IHφ
                          |φ IHφ|φ IHφ|φ IHφ|φ IHφ ψ IHψ]; intros I; cbn [val].
  - right; intros [].
  - left; constructor.
  - destruct I as [a b], (eq_dec a i) as [->|], (eq_dec b i) as [->|];
      [left; reflexivity|right; congruence..].
  - destruct (IHφ I), (IHψ I); first [left; tauto|right; tauto].
  - destruct (IHφ I), (IHψ I); first [left; tauto|right; tauto].
  - destruct (IHφ I), (IHψ I); first [left; tauto|right; tauto].
  - destruct (IHφ I); first [left; tauto|right; tauto].
  - apply forall_sub_dec, IHφ.
  - apply exists_sub_dec, IHφ.
  - apply forall_sub_dec; intros J; destruct (IHφ J); first [left; tauto|right; tauto].
  - apply forall_sub_dec; intros J.
    destruct (IHφ J), (IHψ J); first [left; tauto|right; tauto].
Qed.

Definition entails n (φ ψ : form) : Prop := forall I, isInt n I -> val φ I -> val ψ I.


(** [φ ⊨_n ψ]: on [T_n], [ψ] is true wherever [φ] is. *)
Notation "φ ⊨_ n ψ" := (entails n φ ψ)
  (at level 70, n at level 0, no associativity, format "φ  ⊨_ n  ψ") : itl_scope.

(** ** Validity and [Θ_n] *)

(** [validity n φ]: [φ] is valid, i.e. true on every interval of [T_n]. *)
Definition validity n (φ : form) : Prop := forall I, isInt n I -> val φ I.

(** [φ] and [ψ] are equivalent when they are true on the same intervals of [T_n]. *)
Definition equiv n (φ ψ : form) : Prop := forall I, isInt n I -> (val φ I <-> val ψ I).

(** [Θ_n]: the formulas of [ITL_n] that, true on an interval, are true on all its subintervals. *)
Definition Theta n (φ : form) : Prop := vars_in n φ /\ validity n (φ → □ φ).

(** ** The type [Θ_n]

  An element of [Θ n] is a formula of [ITL_n] together with the proof that
  it is in [Θ_n]; it is used as the formula itself ([fml] is a coercion).
  [Θ_n] contains [⊥], [⊤] and the variables [ε_1, …, ε_n], and is closed
  under [∨] and [∧] (Proposition 3.1 of the paper) and under [∼] and [⇝]
  (left to the reader there). It is not closed under [¬] and [→]
  (Propositions 3.2 and 3.3), so these are not operations of [Θ n]. *)

Record Θ n : Set := mkΘ { fml :> form; fml_Theta : Theta n fml }.

Arguments mkΘ {n}.
Arguments fml {n}.
Arguments fml_Theta {n}.


(** *** Intervals and persistence *)


(** [□] is idempotent *)
Lemma box_idem φ I : val (□ □ φ) I <-> val (□ φ) I.
Proof.
  split.
  - intros H J HJ; exact (H J HJ J (sub_self J I HJ)).
  - intros H J HJ K HK; exact (H K (sub_trans K J I HK HJ)).
Qed.

(** A formula of [Θ_n] true on an interval of [T_n] is true on its
  subintervals: this is what [φ → □ φ] valid says. *)
Lemma Theta_down n φ I J : Theta n φ -> isInt n I -> val φ I -> J ⊆ I -> val φ J.
Proof. intros [_ P] HI Hφ HJ; exact (P I HI Hφ J HJ). Qed.

Section Closure.

Variable n : nat.

Lemma Theta_bot : Theta n ⊥.
Proof. split; [constructor|intros K _ []]. Qed.

Lemma Theta_top : Theta n ⊤.
Proof. split; [constructor|intros K _ _ J _; constructor]. Qed.

Lemma Theta_var i : 1 <= i <= n -> Theta n (ε i).
Proof.
  intros Hi; split; [exact Hi|].
  intros K _ HK J HJ; cbn in HK |- *; subst K; exact (sub_point J i HJ).
Qed.

(** Proposition 3.1: if [φ, ψ ∈ Θ_n], then
  [φ ∧ ψ, φ ∨ ψ ∈ Θ_n]. *)
Proposition Theta_and_or φ ψ :
  Theta n φ -> Theta n ψ -> Theta n (φ ∧ ψ) /\ Theta n (φ ∨ ψ).
Proof.
  intros [Vφ Pφ] [Vψ Pψ]; split; (split; [split; assumption|]).
  - intros K HK [Hφ Hψ] J HJ; split.
    + exact (Pφ K HK Hφ J HJ).
    + exact (Pψ K HK Hψ J HJ).
  - intros K HK [Hφ|Hψ] J HJ.
    + left; exact (Pφ K HK Hφ J HJ).
    + right; exact (Pψ K HK Hψ J HJ).
Qed.

(** [Θ_n] is closed under [∼] and [⇝], which the paper leaves to the reader
  after defining them. These two connectives speak about all the
  subintervals, so only the variables matter. *)
Lemma Theta_pneg φ : vars_in n φ -> Theta n (∼ φ).
Proof.
  intros Vφ; split; [exact Vφ|].
  intros K _ H J HJ L HL; exact (H L (sub_trans L J K HL HJ)).
Qed.

Lemma Theta_pimp φ ψ : vars_in n φ -> vars_in n ψ -> Theta n (φ ⇝ ψ).
Proof.
  intros Vφ Vψ; split; [split; assumption|].
  intros K _ H J HJ L HL; exact (H L (sub_trans L J K HL HJ)).
Qed.

Definition Θbot : Θ n := mkΘ ⊥ Theta_bot.

Definition Θtop : Θ n := mkΘ ⊤ Theta_top.

Definition Θvar i (Hi : 1 <= i <= n) : Θ n := mkΘ (ε i) (Theta_var i Hi).

Definition Θand (φ ψ : Θ n) : Θ n :=
  mkΘ (φ ∧ ψ) (proj1 (Theta_and_or φ ψ (fml_Theta φ) (fml_Theta ψ))).

Definition Θor (φ ψ : Θ n) : Θ n :=
  mkΘ (φ ∨ ψ) (proj2 (Theta_and_or φ ψ (fml_Theta φ) (fml_Theta ψ))).

Definition Θpneg (φ : Θ n) : Θ n :=
  mkΘ (∼ φ) (Theta_pneg φ (proj1 (fml_Theta φ))).

Definition Θpimp (φ ψ : Θ n) : Θ n :=
  mkΘ (φ ⇝ ψ) (Theta_pimp φ ψ (proj1 (fml_Theta φ)) (proj1 (fml_Theta ψ))).

End Closure.

Arguments Θand {n}.
Arguments Θor {n}.
Arguments Θpneg {n}.
Arguments Θpimp {n}.

(** ** Negation and implication
  The classical [¬] and [→] leave [Θ_n]; the pseudo-negation [∼] behaves
  like an intuitionistic negation.
*)
Section PseudoRelativeNegation.

Variable n : nat.

(** Proposition 3.2: [Θ_n] is not closed under [¬]; [φ = ε_1 ∨ ε_2] is in [Θ_n] but [¬ φ] is not. *)
Proposition Theta_not_neg_closed : 2 <= n -> exists φ, Theta n φ /\ ~ Theta n (¬ φ).
Proof.
  intros Hn; exists (ε 1 ∨ ε 2); split; [apply Theta_and_or; apply Theta_var; lia|].
  intros [_ P].
  apply (P (Itv 1 2) ltac:(unfold isInt; cbn; lia) ltac:(cbn; intros [E|E]; discriminate E)
           (Itv 1 1) ltac:(unfold sub; cbn; lia)).
  left; reflexivity.
Qed.

(** Proposition 3.3: [Θ_n] is not closed under [→].
  The paper takes [φ = ε_1 ∨ ε_2], [ψ = ε_2], [I = [t_2, t_3]] and
  [J = [t_2, t_2]]; but [ψ] is true on [J], so [φ → ψ] is true there too.
  The same [φ] and [ψ] work with [I = [t_1, t_2]] and [J = [t_1, t_1]]: [φ]
  is false on [I], so [φ → ψ] is true on [I], while on [J] [φ] is true and
  [ψ] false.
*)
Proposition Theta_not_imp_closed :
  2 <= n -> exists φ ψ, Theta n φ /\ Theta n ψ /\ ~ Theta n (φ → ψ).
Proof.
  intros Hn; exists (ε 1 ∨ ε 2), (ε 2).
  split; [apply Theta_and_or; apply Theta_var; lia|split; [apply Theta_var; lia|]].
  intros [_ P].
  assert (H : val ((ε 1 ∨ ε 2) → ε 2) (Itv 1 2)).
  { cbn; intros [E|E]; discriminate E. }
  assert (HJ : val (ε 1 ∨ ε 2) (Itv 1 1)) by (left; reflexivity).
  pose proof (P (Itv 1 2) ltac:(unfold isInt; cbn; lia) H (Itv 1 1) ltac:(unfold sub; cbn; lia) HJ) as E.
  discriminate E.
Qed.

(** Proposition 3.4, first part: for [φ ∈ Θ_n], if
  [φ] is true on [I], then so is [∼∼ φ].
*)
Proposition pneg_pneg_intro φ I : Theta n φ -> isInt n I -> val φ I -> val (∼ ∼ φ) I.
Proof.
  intros Hφ HI Hv J HJ H.
  exact (H J (sub_self J I HJ) (Theta_down n φ I J Hφ HI Hv HJ)).
Qed.

(** Proposition 3.4, second part: the converse does
  not hold in general; [∼∼ (ε_1 ∨ ε_2)] is true on [[t_1, t_2]], where
  [ε_1 ∨ ε_2] is false.
*)
Proposition pneg_pneg_not_elim :
  2 <= n -> exists φ I, Theta n φ /\ isInt n I /\ val (∼ ∼ φ) I /\ ~ val φ I.
Proof.
  intros Hn; exists (ε 1 ∨ ε 2), (Itv 1 2).
  split; [apply Theta_and_or; apply Theta_var; lia|split; [unfold isInt; cbn; lia|split; [|cbn; intros [E|E]; discriminate E]]].
  intros [a b] HJ H; unfold sub in HJ; cbn in HJ.
  apply (H (Itv a a)); [unfold sub; cbn; lia|].
  assert (a = 1 \/ a = 2) as [-> | ->] by lia; [left|right]; reflexivity.
Qed.

(** Proposition 3.5: for [φ ∈ Θ_n], [∼ φ] and
  [∼∼∼ φ] are true on the same intervals.
*)
Proposition pneg_pneg_pneg φ I :
  Theta n φ -> isInt n I -> (val (∼ φ) I <-> val (∼ ∼ ∼ φ) I).
Proof.
  intros Hφ HI; split.
  - apply pneg_pneg_intro; [apply Theta_pneg, (proj1 Hφ)|exact HI].
  - intros H J HJ Hv.
    exact (H J HJ (pneg_pneg_intro φ J Hφ (isInt_sub n J I HI HJ) Hv)).
Qed.

End PseudoRelativeNegation.

(** Proposition 3.6: for [φ, ψ ∈ Θ_n],
  [[φ] ⇝ [ψ] = ⋁ { [α] ∈ Θ_n/⟺ | [φ] ∧ [α] ≤ [ψ] }], i.e. [⇝] is the
  relative pseudo-complement of [[Θ_n]]. As in the paper's proof, this is
  stated as: [φ ⇝ ψ] belongs to that set, and it lies above every element
  of it, so it is its greatest element, hence its join. *)
Proposition pimp_rel_pcompl n (φ ψ : Θ n) :
  φ ∧ (φ ⇝ ψ) ⊨_n ψ /\
  forall α : Θ n, φ ∧ α ⊨_n ψ -> α ⊨_n φ ⇝ ψ.
Proof.
  split.
  - intros I HI [Hφ H]; exact (H I (isInt_self n I HI) Hφ).
  - intros α Hα I HI Hv J HJ Hφ.
    apply (Hα J (isInt_sub n J I HI HJ)); split; [exact Hφ|].
    exact (Theta_down n α I J (fml_Theta α) HI Hv HJ).
Qed.

End Semantics.