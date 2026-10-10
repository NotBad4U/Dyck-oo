(** * The logic of subintervals [ITL_n] (§ 3, "The logic of subintervals") *)

From Stdlib Require Import Arith Lia List.
Import Nat.

(** ** Intervals of [T_n] *)

(** [Itv i j] is the interval [[t_i, t_j] = { t | t_i ≤ t ≤ t_j }]. *)
Record interval := Itv { lo : nat; hi : nat }.

(** [Int n I]: [I] is an interval of [T_n]. *)
Definition Int n (I : interval) : Prop := 1 <= lo I /\ lo I <= hi I /\ hi I <= n.

(** [J ⊆ I]: [J] is a subinterval of [I]. *)
Definition sub (J I : interval) : Prop :=
  lo I <= lo J /\ lo J <= hi J /\ hi J <= hi I.

Declare Scope itl_scope.
Delimit Scope itl_scope with itl.
Open Scope itl_scope.

Notation "J ⊆ I" := (sub J I) (at level 70, no associativity) : itl_scope.

(** ** Syntax *)

(** The formulas of the language; [FVar i] is the propositional variable
  [ε_i]. *)
Inductive form : Set :=
| FBot
| FTop
| FVar (i : nat)
| FOr (φ ψ : form)
| FAnd (φ ψ : form)
| FImp (φ ψ : form)
| FNeg (φ : form)
| FBox (φ : form)
| FDia (φ : form)
| FPNeg (φ : form)
| FPImp (φ ψ : form).

Bind Scope itl_scope with form.

Notation "⊥" := FBot : itl_scope.
Notation "⊤" := FTop : itl_scope.
Notation "φ ∨ ψ" := (FOr φ ψ) (at level 50, left associativity) : itl_scope.
Notation "φ ∧ ψ" := (FAnd φ ψ) (at level 40, left associativity) : itl_scope.
Notation "φ → ψ" := (FImp φ ψ) (at level 60, right associativity) : itl_scope.
Notation "¬ φ" := (FNeg φ) (at level 35, right associativity) : itl_scope.
Notation "□ φ" := (FBox φ) (at level 35, right associativity) : itl_scope.
Notation "◇ φ" := (FDia φ) (at level 35, right associativity) : itl_scope.
Notation "∼ φ" := (FPNeg φ) (at level 35, right associativity) : itl_scope.
Notation "φ ⇝ ψ" := (FPImp φ ψ) (at level 60, right associativity) : itl_scope.

(** [vars_in n φ]: the variables of [φ] are among [ε_1, …, ε_n], i.e.
  [φ ∈ ITL_n]. *)
Fixpoint vars_in n (φ : form) : Prop :=
  match φ with
  | ⊥ | ⊤ => True
  | FVar i => 1 <= i <= n
  | φ ∨ ψ | φ ∧ ψ | φ → ψ | φ ⇝ ψ => vars_in n φ /\ vars_in n ψ
  | ¬ φ | □ φ | ◇ φ | ∼ φ => vars_in n φ
  end.

(** ** Semantics *)

(** [val φ I]: [φ] is true on the interval [I]. In particular [ε_i] is true
  exactly on the one-point interval [[t_i, t_i]]. *)
Fixpoint val (φ : form) (I : interval) : Prop :=
  match φ with
  | ⊥ => False
  | ⊤ => True
  | FVar i => I = Itv i i
  | φ ∨ ψ => val φ I \/ val ψ I
  | φ ∧ ψ => val φ I /\ val ψ I
  | φ → ψ => val φ I -> val ψ I
  | ¬ φ => ~ val φ I
  | □ φ => forall J, J ⊆ I -> val φ J
  | ◇ φ => exists J, J ⊆ I /\ val φ J
  | ∼ φ => forall J, J ⊆ I -> ~ val φ J
  | φ ⇝ ψ => forall J, J ⊆ I -> val φ J -> val ψ J
  end.

(** ** Validity and [Θ_n] *)

(** [φ] is valid when it is true on every interval of [T_n]. *)
Definition valid n (φ : form) : Prop := forall I, Int n I -> val φ I.

(** [φ] and [ψ] are equivalent when they are true on the same intervals of
  [T_n]. *)
Definition equiv n (φ ψ : form) : Prop := forall I, Int n I -> (val φ I <-> val ψ I).

(** [Θ_n]: the formulas of [ITL_n] that, true on an interval, are true on all
  its subintervals. *)
Definition Theta n (φ : form) : Prop := vars_in n φ /\ valid n (φ → □ φ).

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

Lemma sub_trans K J I : K ⊆ J -> J ⊆ I -> K ⊆ I.
Proof. unfold sub; lia. Qed.

Lemma sub_self J I : J ⊆ I -> J ⊆ J.
Proof. unfold sub; lia. Qed.

Lemma Int_self n I : Int n I -> I ⊆ I.
Proof. unfold Int, sub; lia. Qed.

(** A subinterval of an interval of [T_n] is an interval of [T_n]. *)
Lemma Int_sub n J I : Int n I -> J ⊆ I -> Int n J.
Proof. unfold Int, sub; lia. Qed.

(** The only subinterval of [[t_i, t_i]] is itself. *)
Lemma sub_point J i : J ⊆ Itv i i -> J = Itv i i.
Proof. destruct J as [a b]; unfold sub; cbn; intros H; f_equal; lia. Qed.

(** A formula of [Θ_n] true on an interval of [T_n] is true on its
  subintervals: this is what [φ → □ φ] valid says. *)
Lemma Theta_down n φ I J : Theta n φ -> Int n I -> val φ I -> J ⊆ I -> val φ J.
Proof. intros [_ P] HI Hφ HJ; exact (P I HI Hφ J HJ). Qed.

Section Closure.

Variable n : nat.

Lemma Theta_bot : Theta n ⊥.
Proof. split; [constructor|intros K _ []]. Qed.

Lemma Theta_top : Theta n ⊤.
Proof. split; [constructor|intros K _ _ J _; constructor]. Qed.

Lemma Theta_var i : 1 <= i <= n -> Theta n (FVar i).
Proof.
  intros Hi; split; [exact Hi|].
  intros K _ HK J HJ; cbn in HK |- *; subst K; exact (sub_point J i HJ).
Qed.

(** Proposition 3.1 of [Ferrari2015DyckAI]: if [φ, ψ ∈ Θ_n], then
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

Definition Θvar i (Hi : 1 <= i <= n) : Θ n := mkΘ (FVar i) (Theta_var i Hi).

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
  like an intuitionistic negation. The counterexamples use the variables
  [ε_1] and [ε_2], hence [n ≥ 2]. *)

Section Negation.

Variable n : nat.

(** [ε_1 ∨ ε_2] is in [Θ_n], and false on [[t_1, t_2]] while true on
  [[t_1, t_1]]. *)
Lemma Theta_e12 : 2 <= n -> Theta n (FVar 1 ∨ FVar 2).
Proof.
  intros Hn; apply Theta_and_or; apply Theta_var; lia.
Qed.

Lemma Int_12 : 2 <= n -> Int n (Itv 1 2).
Proof. unfold Int; cbn; lia. Qed.

Lemma val_e12_12 : ~ val (FVar 1 ∨ FVar 2) (Itv 1 2).
Proof. cbn; intros [E|E]; discriminate E. Qed.

Lemma sub_11_12 : Itv 1 1 ⊆ Itv 1 2.
Proof. unfold sub; cbn; lia. Qed.

(** Proposition 3.2 of [Ferrari2015DyckAI]: [Θ_n] is not closed under [¬];
  [φ = ε_1 ∨ ε_2] is in [Θ_n] but [¬ φ] is not. *)
Proposition Theta_not_neg_closed : 2 <= n -> exists φ, Theta n φ /\ ~ Theta n (¬ φ).
Proof.
  intros Hn; exists (FVar 1 ∨ FVar 2); split; [exact (Theta_e12 Hn)|].
  intros [_ P].
  apply (P (Itv 1 2) (Int_12 Hn) val_e12_12 (Itv 1 1) sub_11_12).
  left; reflexivity.
Qed.

(** Proposition 3.3 of [Ferrari2015DyckAI]: [Θ_n] is not closed under [→].
  The paper takes [φ = ε_1 ∨ ε_2], [ψ = ε_2], [I = [t_2, t_3]] and
  [J = [t_2, t_2]]; but [ψ] is true on [J], so [φ → ψ] is true there too.
  The same [φ] and [ψ] work with [I = [t_1, t_2]] and [J = [t_1, t_1]]: [φ]
  is false on [I], so [φ → ψ] is true on [I], while on [J] [φ] is true and
  [ψ] false. *)
Proposition Theta_not_imp_closed :
  2 <= n -> exists φ ψ, Theta n φ /\ Theta n ψ /\ ~ Theta n (φ → ψ).
Proof.
  intros Hn; exists (FVar 1 ∨ FVar 2), (FVar 2).
  split; [exact (Theta_e12 Hn)|split; [apply Theta_var; lia|]].
  intros [_ P].
  assert (H : val ((FVar 1 ∨ FVar 2) → FVar 2) (Itv 1 2)).
  { intros Hφ; contradiction (val_e12_12 Hφ). }
  assert (HJ : val (FVar 1 ∨ FVar 2) (Itv 1 1)) by (left; reflexivity).
  pose proof (P (Itv 1 2) (Int_12 Hn) H (Itv 1 1) sub_11_12 HJ) as E.
  discriminate E.
Qed.

(** Proposition 3.4 of [Ferrari2015DyckAI], first part: for [φ ∈ Θ_n], if
  [φ] is true on [I], then so is [∼∼ φ]. *)
Proposition pneg_pneg_intro φ I : Theta n φ -> Int n I -> val φ I -> val (∼ ∼ φ) I.
Proof.
  intros Hφ HI Hv J HJ H.
  exact (H J (sub_self J I HJ) (Theta_down n φ I J Hφ HI Hv HJ)).
Qed.

(** Proposition 3.4 of [Ferrari2015DyckAI], second part: the converse does
  not hold in general; [∼∼ (ε_1 ∨ ε_2)] is true on [[t_1, t_2]], where
  [ε_1 ∨ ε_2] is false. *)
Proposition pneg_pneg_not_elim :
  2 <= n -> exists φ I, Theta n φ /\ Int n I /\ val (∼ ∼ φ) I /\ ~ val φ I.
Proof.
  intros Hn; exists (FVar 1 ∨ FVar 2), (Itv 1 2).
  split; [exact (Theta_e12 Hn)|split; [exact (Int_12 Hn)|split; [|exact val_e12_12]]].
  intros [a b] HJ H; unfold sub in HJ; cbn in HJ.
  apply (H (Itv a a)); [unfold sub; cbn; lia|].
  assert (a = 1 \/ a = 2) as [-> | ->] by lia; [left|right]; reflexivity.
Qed.

(** Proposition 3.5 of [Ferrari2015DyckAI]: for [φ ∈ Θ_n], [∼ φ] and
  [∼∼∼ φ] are true on the same intervals. *)
Proposition pneg_pneg_pneg φ I :
  Theta n φ -> Int n I -> (val (∼ φ) I <-> val (∼ ∼ ∼ φ) I).
Proof.
  intros Hφ HI; split.
  - apply pneg_pneg_intro; [apply Theta_pneg, (proj1 Hφ)|exact HI].
  - intros H J HJ Hv.
    exact (H J HJ (pneg_pneg_intro φ J Hφ (Int_sub n J I HI HJ) Hv)).
Qed.

End Negation.

(** ** The pseudo-implication in [[Θ_n]]

  Formulas of [Θ_n] are compared by the order of the paper's proof of
  Proposition 3.6: [[φ] ≤ [ψ]] when [ψ] is true on every interval of [T_n]
  where [φ] is. Two formulas are equivalent ([equiv]) when each is below the
  other. *)

Definition entails n (φ ψ : form) : Prop := forall I, Int n I -> val φ I -> val ψ I.

(** [φ ⊨_n ψ]: on [T_n], [ψ] is true wherever [φ] is. This is a semantic
  consequence: there is no proof system here. *)
Notation "φ ⊨_ n ψ" := (entails n φ ψ)
  (at level 70, n at level 0, no associativity, format "φ  ⊨_ n  ψ") : itl_scope.

(** Proposition 3.6 of [Ferrari2015DyckAI]: for [φ, ψ ∈ Θ_n],
  [[φ] ⇝ [ψ] = ⋁ { [α] ∈ Θ_n/⟺ | [φ] ∧ [α] ≤ [ψ] }], i.e. [⇝] is the
  relative pseudo-complement of [[Θ_n]]. As in the paper's proof, this is
  stated as: [φ ⇝ ψ] belongs to that set, and it lies above every element
  of it, so it is its greatest element, hence its join. *)
Proposition pimp_rel_pcompl n (φ ψ : Θ n) :
  φ ∧ (φ ⇝ ψ) ⊨_n ψ /\
  forall α : Θ n, φ ∧ α ⊨_n ψ -> α ⊨_n φ ⇝ ψ.
Proof.
  split.
  - intros I HI [Hφ H]; exact (H I (Int_self n I HI) Hφ).
  - intros α Hα I HI Hv J HJ Hφ.
    apply (Hα J (Int_sub n J I HI HJ)); split; [exact Hφ|].
    exact (Theta_down n α I J (fml_Theta α) HI Hv HJ).
Qed.

(** ** Decidability

  The paper's valuation is two-valued: a formula is either true or false on
  an interval. With [val] in [Prop] this is a theorem, [val_dec]: an
  interval has finitely many subintervals ([subs]), so the modal clauses
  only quantify over a finite list. *)

(** The subintervals of [I]. *)
Definition subs (I : interval) : list interval :=
  flat_map (fun a => map (Itv a) (seq a (S (hi I) - a)))
    (seq (lo I) (S (hi I) - lo I)).

Lemma in_subs J I : In J (subs I) <-> J ⊆ I.
Proof.
  destruct J as [a b]; unfold subs, sub; cbn [lo hi]; rewrite in_flat_map; split.
  - intros [a' [Ha' Hb]]; apply in_seq in Ha'.
    apply in_map_iff in Hb as [b' [E Hb']]; injection E as -> ->.
    apply in_seq in Hb'; lia.
  - intros H; exists a; split; [apply in_seq; lia|].
    apply in_map_iff; exists b; split; [reflexivity|apply in_seq; lia].
Qed.

Lemma forall_sub_dec (P : interval -> Prop) I :
  (forall J, {P J} + {~ P J}) ->
  {forall J, J ⊆ I -> P J} + {~ forall J, J ⊆ I -> P J}.
Proof.
  intros Pd; destruct (Forall_dec P Pd (subs I)) as [H|H];
    rewrite Forall_forall in H.
  - left; intros J HJ; apply H, in_subs, HJ.
  - right; intros H'; apply H; intros J HJ; apply H', in_subs, HJ.
Qed.

Lemma exists_sub_dec (P : interval -> Prop) I :
  (forall J, {P J} + {~ P J}) ->
  {exists J, J ⊆ I /\ P J} + {~ exists J, J ⊆ I /\ P J}.
Proof.
  intros Pd; destruct (Exists_dec P (subs I) Pd) as [H|H];
    rewrite Exists_exists in H.
  - left; destruct H as [J [HJ HP]]; exists J; split; [apply in_subs, HJ|exact HP].
  - right; intros [J [HJ HP]]; apply H; exists J; split; [apply in_subs, HJ|exact HP].
Qed.

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
