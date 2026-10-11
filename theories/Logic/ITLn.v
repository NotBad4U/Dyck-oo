(** * The logic of subintervals [ITL_n] (§ 3, "The logic of subintervals") *)

From Stdlib Require Import Arith Lia RelationClasses Morphisms.
Import Nat.
From Dyck Require Import Lattice Interval.

Declare Scope itl_scope.
Delimit Scope itl_scope with itl.
Open Scope itl_scope.

Section Syntax.

(** The formulas of the language *)
Inductive form : Set :=
| FBot
| FTop
| FVar (i : nat) (* propositional variable [ε_i] *)
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

Notation "φ ⊨_ n ψ" := (entails n φ ψ)
  (at level 70, n at level 0, no associativity, format "φ  ⊨_ n  ψ") : itl_scope.

(** [φ] is valid means true on every interval of [T_n]. *)
Definition valid n (φ : form) : Prop := forall I, isInt n I -> val φ I.

Definition equiv n (φ ψ : form) : Prop := forall I, isInt n I -> (val φ I <-> val ψ I).

Notation "φ ≊_ n ψ" := (equiv n φ ψ)
  (at level 70, n at level 0, no associativity, format "φ  ≊_ n  ψ") : itl_scope.
 
(**
  We define [Θ_n = {φ ∈ ITL_n | valid of φ → □ φ }].
  Intuitively, this means that, if [φ] is [true] in [I], then [φ] is true in all subintervals of I. 
*)
Definition Theta n (φ : form) : Prop := vars_in n φ /\ valid n (φ → □ φ).

Record Θ n : Set := mkΘ { fml :> form; fml_Theta : Theta n fml }.

Arguments mkΘ {n}.
Arguments fml {n}.
Arguments fml_Theta {n}.

Lemma val_box_idem φ I : val (□ □ φ) I <-> val (□ φ) I.
Proof. exact (interior_idem (val φ) I). Qed.

(** A formula of [Θ_n] true on an interval of [T_n] is true on its subintervals *)
Lemma Theta_down n φ I J : Theta n φ -> isInt n I -> val φ I -> J ⊆ I -> val φ J.
Proof. intros [_ P] HI Hφ HJ; exact (P I HI Hφ J HJ). Qed.

Lemma Theta_bot n : Theta n ⊥.
Proof. split; [constructor|intros K _ []]. Qed.

Lemma Theta_top n : Theta n ⊤.
Proof. split; [constructor|intros K _ _ J _; constructor]. Qed.

Lemma Theta_var n i : 1 <= i <= n -> Theta n (ε i).
Proof.
  intros Hi; split; [exact Hi|].
  intros K _ HK J HJ; cbn in HK |- *; subst K; exact (sub_point J i HJ).
Qed.

(** ** Propositions 3.1–3.5

  - [Θ_n] is closed under [∧] and [∨];
  - the classical [¬] and [→] leave it;
  - the pseudo-negation [∼] behaves like an intuitionistic negation;
  - [≊_n] is a congruence (left to the reader).

  Proposition 3.6 is about the classes [[Θ_n]], built in the next section.
*)
Section Propositions.

(** Proposition 3.1: if [φ, ψ ∈ Θ_n], then [φ ∧ ψ, φ ∨ ψ ∈ Θ_n]. *)
Proposition Theta_and_or n φ ψ : Theta n φ -> Theta n ψ -> Theta n (φ ∧ ψ) /\ Theta n (φ ∨ ψ).
Proof.
  intros [Vφ Pφ] [Vψ Pψ]; split; (split; [split; assumption|]).
  - intros K HK [Hφ Hψ] J HJ; split.
    + exact (Pφ K HK Hφ J HJ).
    + exact (Pψ K HK Hψ J HJ).
  - intros K HK [Hφ|Hψ] J HJ.
    + left; exact (Pφ K HK Hφ J HJ).
    + right; exact (Pψ K HK Hψ J HJ).
Qed.

(** Proposition 3.2: [Θ_n] is not closed under [¬]; [φ = ε_1 ∨ ε_2] is in [Θ_n] but [¬ φ] is not. *)
Proposition Theta_not_neg_closed n : 2 <= n -> exists φ, Theta n φ /\ ~ Theta n (¬ φ).
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
*)
Proposition Theta_not_imp_closed n :
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

(** Proposition 3.4 (i): for [φ ∈ Θ_n], if [φ] is true on [I], then so is [∼∼ φ]. *)
Proposition pneg_pneg_intro n φ I : Theta n φ -> isInt n I -> val φ I -> val (∼ ∼ φ) I.
Proof.
  intros Hφ HI Hv J HJ H.
  exact (H J (sub_self J I HJ) (Theta_down n φ I J Hφ HI Hv HJ)).
Qed.

(** Proposition 3.4 (ii), the converse does not hold in general because
  [∼∼ (ε_1 ∨ ε_2)] is true on [[t_1, t_2]], where [ε_1 ∨ ε_2] is false.
*)
Proposition pneg_pneg_not_elim n :
  2 <= n -> exists φ I, Theta n φ /\ isInt n I /\ val (∼ ∼ φ) I /\ ~ val φ I.
Proof.
  intros Hn; exists (ε 1 ∨ ε 2), (Itv 1 2).
  split; [apply Theta_and_or; apply Theta_var; lia|split; [unfold isInt; cbn; lia|split; [|cbn; intros [E|E]; discriminate E]]].
  intros [a b] HJ H; unfold sub in HJ; cbn in HJ.
  apply (H (Itv a a)); [unfold sub; cbn; lia|].
  assert (a = 1 \/ a = 2) as [-> | ->] by lia; [left|right]; reflexivity.
Qed.

(** Proposition 3.5: for [φ ∈ Θ_n], [∼ φ] iff [∼∼∼ φ] are true on the same intervals.  *)
Proposition pneg_pneg_pneg n φ I :
  Theta n φ -> isInt n I -> (val (∼ φ) I <-> val (∼ ∼ ∼ φ) I).
Proof.
  intros Hφ HI; split.
  - intros H J HJ H2; apply (H2 J (sub_self J I HJ)).
    intros K HK Hv; exact (H K (sub_trans K J I HK HJ) Hv).
  - intros H J HJ Hv.
    exact (H J HJ (pneg_pneg_intro n φ J Hφ (isInt_sub n J I HI HJ) Hv)).
Qed.

(** [≊_n] is an equivalence relation, and it preserves [∨], [∧], [⇝] and [∼]. *)
#[export] Instance equiv_Equivalence n : Equivalence (equiv n).
Proof.
  split.
  - intros φ I _; split; intros H; exact H.
  - intros φ ψ H I HI; exact (iff_sym (H I HI)).
  - intros φ ψ χ H1 H2 I HI; split; intros H.
    + apply (H2 I HI), (H1 I HI), H.
    + apply (H1 I HI), (H2 I HI), H.
Qed.

Lemma equiv_or n φ φ' ψ ψ' : φ ≊_n φ' -> ψ ≊_n ψ' -> φ ∨ ψ ≊_n φ' ∨ ψ'.
Proof. intros Hφ Hψ I HI; specialize (Hφ I HI); specialize (Hψ I HI); cbn; tauto. Qed.

Lemma equiv_and n φ φ' ψ ψ' : φ ≊_n φ' -> ψ ≊_n ψ' -> φ ∧ ψ ≊_n φ' ∧ ψ'.
Proof. intros Hφ Hψ I HI; specialize (Hφ I HI); specialize (Hψ I HI); cbn; tauto. Qed.

Lemma equiv_pimp n φ φ' ψ ψ' : φ ≊_n φ' -> ψ ≊_n ψ' -> φ ⇝ ψ ≊_n φ' ⇝ ψ'.
Proof.
  intros Hφ Hψ I HI; cbn; split; intros H J HJ Hv;
    specialize (Hφ J (isInt_sub n J I HI HJ)); specialize (Hψ J (isInt_sub n J I HI HJ));
    specialize (H J HJ); tauto.
Qed.

Lemma equiv_pneg n φ φ' : φ ≊_n φ' -> ∼ φ ≊_n ∼ φ'.
Proof.
  intros Hφ I HI; cbn; split; intros H J HJ Hv;
    specialize (Hφ J (isInt_sub n J I HI HJ)); specialize (H J HJ); tauto.
Qed.

End Propositions.

(** ** Closure, and the Heyting algebra [[Θ_n]]
  [Θ_n] is closed under [∼] and [⇝]; its classes form a distributive
  lattice, in which [⇝] is the relative pseudo-complement (Proposition 3.6),
  so [[Θ_n]] is a Heyting algebra.
*)
Section Closure.

Proposition Theta_pneg n φ : vars_in n φ -> Theta n (∼ φ).
Proof.
  intros Vφ; split; [exact Vφ|].
  intros K _ H J HJ L HL; exact (H L (sub_trans L J K HL HJ)).
Qed.

Proposition Theta_pimp n φ ψ : vars_in n φ -> vars_in n ψ -> Theta n (φ ⇝ ψ).
Proof.
  intros Vφ Vψ; split; [split; assumption|].
  intros K _ H J HJ L HL; exact (H L (sub_trans L J K HL HJ)).
Qed.

(** [Θ_n] is closed under [□]. *)
Proposition Theta_box n φ : Theta n φ -> Theta n (□ φ).
Proof.
  intros [Vφ Pφ]; split; [exact Vφ|].
  intros K _ H J HJ L HL; exact (H L (sub_trans L J K HL HJ)).
Qed.

Proposition box_Theta_id n φ I : Theta n φ -> isInt n I -> (val (□ φ) I <-> val φ I).
Proof.
  intros Hφ HI; split.
  - intros H; apply H; exact (isInt_self n I HI).
  - intros H J HJ; exact (Theta_down n φ I J Hφ HI H HJ).
Qed.

(** [Θ_n] is not closed under [◇]: [◇ ε_1] holds on [[t_1, t_2]], which
  contains [t_1], but not on its subinterval [[t_2, t_2]]. *)
Proposition Theta_not_dia_closed n : 2 <= n -> exists φ, Theta n φ /\ ~ Theta n (◇ φ).
Proof.
  intros Hn; exists (ε 1); split; [apply Theta_var; lia|].
  intros [_ P].
  destruct (P (Itv 1 2) ltac:(unfold isInt; cbn; lia)
              ltac:(exists (Itv 1 1); split; [unfold sub; cbn; lia|reflexivity])
              (Itv 2 2) ltac:(unfold sub; cbn; lia)) as [J [HJ E]].
  subst J; unfold sub in HJ; cbn in HJ; lia.
Qed.

(* We can now define the operator over Θ_n. *)

Definition Θbot n : Θ n := mkΘ ⊥ (Theta_bot n).
Definition Θtop n : Θ n := mkΘ ⊤ (Theta_top n).
Definition Θvar n i (Hi : 1 <= i <= n) : Θ n := mkΘ (ε i) (Theta_var n i Hi).

Definition Θand {n} (φ ψ : Θ n) : Θ n :=
  mkΘ (φ ∧ ψ) (proj1 (Theta_and_or n φ ψ (fml_Theta φ) (fml_Theta ψ))).

Definition Θor {n} (φ ψ : Θ n) : Θ n :=
  mkΘ (φ ∨ ψ) (proj2 (Theta_and_or n φ ψ (fml_Theta φ) (fml_Theta ψ))).

Definition Θpimp {n} (φ ψ : Θ n) : Θ n :=
  mkΘ (φ ⇝ ψ) (Theta_pimp n φ ψ (proj1 (fml_Theta φ)) (proj1 (fml_Theta ψ))).

Definition Θpneg {n} (φ : Θ n) : Θ n :=
  mkΘ (∼ φ) (Theta_pneg n φ (proj1 (fml_Theta φ))).

Declare Scope Θ_scope.
Delimit Scope Θ_scope with Θ.
Bind Scope Θ_scope with Θ.

Notation "⊥" := (Θbot _) : Θ_scope.
Notation "⊤" := (Θtop _) : Θ_scope.
Notation "φ ∨ ψ" := (Θor φ ψ) (at level 50, left associativity) : Θ_scope.
Notation "φ ∧ ψ" := (Θand φ ψ) (at level 40, left associativity) : Θ_scope.
Notation "φ ⇝ ψ" := (Θpimp φ ψ) (at level 60, right associativity) : Θ_scope.
Notation "∼ φ" := (Θpneg φ) (at level 35, right associativity) : Θ_scope.

(** *** The classes of [Θ_n/≊_n]
  NOTE: Rocq has no quotient types but we can use Setoid relation that we used to define [Poset] in Lattice.v
*)

Record Θcls n : Set := cls { rep : Θ n }.

Arguments cls {n}.
Arguments rep {n}.

Notation "[ φ ]" := (cls φ) : itl_scope.

(** [[φ] ≤ [ψ]] when [φ(I) ≤ ψ(I)] for all intervals [I], and [[φ] ≡ [ψ]] when [φ ≊_n ψ]. *)
#[export] Instance Θcls_Poset n : Poset (Θcls n).
Proof.
  refine {| po_le (a b : Θcls n) := rep a ⊨_n rep b;
            po_eq (a b : Θcls n) := rep a ≊_n rep b |}.
  - split; [intros a I _ H; exact H|intros a b c H1 H2 I HI H; exact (H2 I HI (H1 I HI H))].
  - intros a b; split.
    + intros H; split; intros I HI; apply (H I HI).
    + intros [H1 H2] I HI; split; [exact (H1 I HI)|exact (H2 I HI)].
Defined.

#[export] Instance Θcls_Meet n : Meet (Θcls n).
Proof.
  refine {| meet (a b : Θcls n) := [rep a ∧ rep b] |}.
  intros a b c; split.
  - intros H; split; intros I HI Hc; apply (H I HI Hc).
  - intros [H1 H2] I HI Hc; split; [exact (H1 I HI Hc)|exact (H2 I HI Hc)].
Defined.

#[export] Instance Θcls_Join n : Join (Θcls n).
Proof.
  refine {| join (a b : Θcls n) := [rep a ∨ rep b] |}.
  intros a b c; split.
  - intros H; split; intros I HI Hv; apply (H I HI); cbn; tauto.
  - intros [H1 H2] I HI [Hv|Hv]; [exact (H1 I HI Hv)|exact (H2 I HI Hv)].
Defined.

#[export] Instance Θcls_Bot n : Bot (Θcls n).
Proof. refine {| bot := [⊥] |}; intros a I _ []. Defined.

#[export] Instance Θcls_Top n : Top (Θcls n).
Proof. refine {| top := [⊤] |}; intros a I _ _; exact Logic.I. Defined.

#[export] Instance Θcls_Distributive n : Distributive (Θcls n).
Proof. intros a b c I HI; cbn; tauto. Qed.


Lemma pimp_mp n (φ ψ : Θ n) : [φ] ⊓ [φ ⇝ ψ] ≤ [ψ].
Proof. intros I HI [Hφ H]; exact (H I (isInt_self n I HI) Hφ). Qed.

Lemma pimp_above n (φ ψ : Θ n) A : [φ] ⊓ A ≤ [ψ] -> A ≤ [φ ⇝ ψ].
Proof.
  destruct A as [α]; intros Hα I HI Hv J HJ Hφ.
  apply (Hα J (isInt_sub n J I HI HJ)); split; [exact Hφ|].
  exact (Theta_down n α I J (fml_Theta α) HI Hv HJ).
Qed.

(** Proposition 3.6: for [φ, ψ ∈ Θ_n],

  [[φ] ⇝ [ψ] = ⋁ { [α] ∈ Θ_n/≊_n | [φ] ∧ [α] ≤ [ψ] }],

  In other wrods, [⇝] is the relative pseudocomplement operation
  in the canonical Heyting algebra structure of [Θ_n].
*)
Proposition pimp_rel_pcompl n (φ ψ : Θ n) : is_sup (fun A => [φ] ⊓ A ≤ [ψ]) [φ ⇝ ψ].
Proof. apply greatest_is_sup; [exact (pimp_mp n φ ψ)|exact (pimp_above n φ ψ)]. Qed.

(** By Proposition 3.6, [⇝] is the relative pseudo-complement [⟿] of [[Θ_n]]. *)
#[export] Instance Θcls_RelPseudoComplement n : RelPseudoComplement (Θcls n).
Proof.
  refine {| himp (a b : Θcls n) := [rep a ⇝ rep b] |}.
  intros [φ] [ψ] [χ]; split.
  - exact (pimp_above n φ ψ [χ]).
  - intros H; exact (le_trans (leI2 (lexx [φ]) H) (pimp_mp n φ ψ)).
Defined.

#[export] Instance Θcls_Lattice n : Lattice (Θcls n) :=
  {| lat_Poset := Θcls_Poset n; lat_Meet := Θcls_Meet n; lat_Join := Θcls_Join n |}.

(** [[Θ_n]] is a Heyting algebra. *)
#[export] Instance Θcls_HeytingAlgebra n : HeytingAlgebra (Θcls n) :=
  {| ha_Lattice := Θcls_Lattice n; ha_Bot := Θcls_Bot n; ha_Top := Θcls_Top n;
     ha_Distributive := Θcls_Distributive n;
     ha_RelPseudoComplement := Θcls_RelPseudoComplement n |}.

Lemma cls_ops n (φ ψ : Θ n) :
  [φ] ⊔ [ψ] = [φ ∨ ψ] /\ [φ] ⊓ [ψ] = [φ ∧ ψ] /\ [φ] ⟿ [ψ] = [φ ⇝ ψ].
Proof. repeat split. Qed.

Lemma cls_wd n (a a' b b' : Θcls n) : a ≡ a' -> b ≡ b' ->
  a ⊓ b ≡ a' ⊓ b' /\ a ⊔ b ≡ a' ⊔ b' /\ a ⟿ b ≡ a' ⟿ b'.
Proof.
  intros Ea Eb; split; [|split].
  - exact (equiv_and n _ _ _ _ Ea Eb).
  - exact (equiv_or n _ _ _ _ Ea Eb).
  - exact (equiv_pimp n _ _ _ _ Ea Eb).
Qed.

#[export] Instance cls_himp_Proper n : Proper (po_eq ==> po_eq ==> po_eq) (@himp (Θcls n) _ _ _).
Proof. intros a a' Ea b b' Eb; exact (proj2 (proj2 (cls_wd n a a' b b' Ea Eb))). Qed.

End Closure.

End Semantics.