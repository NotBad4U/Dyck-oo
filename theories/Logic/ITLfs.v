(** * The logic [ℒ_1] of [𝒟_fs] ("Logic of Model 1") *)

From Stdlib Require Import Arith Lia.
Import Nat.
From Dyck Require Import Interval ITLn ITLω.

Section Syntax.

Inductive form1 : Type :=
| Bot1
| Var1 (i : nat)
| And1 (φ ψ : form1)
| Or1 (φ ψ : form1).

End Syntax.

(** Notations as in [ITLn], in a scope of their own. They sit outside
  [Syntax], since a notation declared in a section ends with it. *)
Declare Scope form1_scope.
Delimit Scope form1_scope with form1.
Bind Scope form1_scope with form1.
Open Scope form1_scope.

Notation "⊥" := Bot1 : form1_scope.
Notation "φ ∨ ψ" := (Or1 φ ψ) (at level 50, left associativity) : form1_scope.
Notation "φ ∧ ψ" := (And1 φ ψ) (at level 40, left associativity) : form1_scope.

Section Semantics.

Fixpoint val1 (φ : form1) (I : interval) : Prop :=
  match φ with
  | ⊥ => False
  | Var1 i => I = Itv i i
  | φ ∧ ψ => val1 φ I /\ val1 ψ I
  | φ ∨ ψ => val1 φ I \/ val1 ψ I
  end.

(** [ℒ_1 ⊆ ℒ_ω], with the same truth sets. *)
Fixpoint emb1 (φ : form1) : formω :=
  match φ with
  | ⊥ => ⊥
  | Var1 i => Varω i
  | φ ∧ ψ => emb1 φ ∧ emb1 ψ
  | φ ∨ ψ => emb1 φ ∨ emb1 ψ
  end.

Definition entails1 (φ ψ : form1) : Prop := forall I, Intω I -> val1 φ I -> val1 ψ I.

Notation "φ ⊨_fs ψ" := (entails1 φ ψ) (at level 70, no associativity) : form1_scope.

Lemma valω_emb1 φ I : valω (emb1 φ) I <-> val1 φ I.
Proof.
  induction φ as [|i|φ IHφ ψ IHψ|φ IHφ ψ IHψ]; cbn [emb1 valω val1].
  - reflexivity.
  - reflexivity.
  - split; intros [H1 H2]; split; [apply IHφ|apply IHψ|apply IHφ|apply IHψ]; assumption.
  - split; intros [H|H]; [left; apply IHφ|right; apply IHψ|left; apply IHφ|right; apply IHψ]; assumption.
Qed.

Lemma val1_persistent φ I J : val1 φ I -> J ⊆ I -> val1 φ J.
Proof.
  intros HI HJ; apply valω_emb1; apply valω_emb1 in HI.
  exact (valω_persistent (emb1 φ) I J HI HJ).
Qed.

(** The largest variable of a formula bounds the intervals where it holds. *)
Fixpoint bound1 (φ : form1) : nat :=
  match φ with
  | ⊥ => 0
  | Var1 i => i
  | φ ∧ ψ | φ ∨ ψ => max (bound1 φ) (bound1 ψ)
  end.

Lemma val1_le_bound φ I : val1 φ I -> hi I <= bound1 φ.
Proof.
  induction φ as [|i|φ IHφ ψ IHψ|φ IHφ ψ IHψ]; cbn [val1 bound1]; intros H.
  - destruct H.
  - subst I; cbn [hi]; lia.
  - destruct H as [H _]; specialize (IHφ H); lia.
  - destruct H as [H|H]; [specialize (IHφ H)|specialize (IHψ H)]; lia.
Qed.

(** Every formula of [ℒ_1] has finite support. *)
Theorem val1_bounded φ : bounded (val1 φ).
Proof. exists (bound1 φ); intros I _ H; exact (val1_le_bound φ I H). Qed.

Definition valid1 (φ : form1) : Prop := forall I, Intω I -> val1 φ I.

(** *** [∼], [⇝], [□], [◇] on Model 1

  Read in [ℒ_ω], [∼ φ] and [φ ⇝ ψ] hold on every interval beyond the bound
  of [φ], where [φ] is false: their truth sets are unbounded, so no formula
  of [ℒ_1] is equivalent to them ([∼ ⊥ ≡ ⊤] and [⊥ ⇝ ⊥ ≡ ⊤] being the
  extreme cases). [□] is the identity on [ℒ_1]; [◇] breaks persistence. *)
Lemma pneg1_unbounded φ : unbounded (valω (∼ emb1 φ)).
Proof.
  intros N; exists (Itv (S (N + bound1 φ)) (S (N + bound1 φ))).
  split; [unfold Intω; cbn; lia|split; [cbn; lia|]].
  intros J HJ Hv; apply valω_emb1, val1_le_bound in Hv.
  unfold sub in HJ; cbn in HJ; lia.
Qed.

Lemma pimp1_unbounded φ ψ : unbounded (valω (emb1 φ ⇝ emb1 ψ)).
Proof.
  intros N; exists (Itv (S (N + bound1 φ)) (S (N + bound1 φ))).
  split; [unfold Intω; cbn; lia|split; [cbn; lia|]].
  intros J HJ Hv; apply valω_emb1, val1_le_bound in Hv.
  unfold sub in HJ; cbn in HJ; exfalso; lia.
Qed.

Theorem pneg_not_closed1 φ :
  ~ exists χ : form1, forall I, Intω I -> (val1 χ I <-> valω (∼ emb1 φ) I).
Proof.
  intros [χ Hχ]; apply (unbounded_not_bounded _ (pneg1_unbounded φ)).
  destruct (val1_bounded χ) as [N HN]; exists N.
  intros I HI Hv; exact (HN I HI (proj2 (Hχ I HI) Hv)).
Qed.

Theorem pimp_not_closed1 φ ψ :
  ~ exists χ : form1, forall I, Intω I -> (val1 χ I <-> valω (emb1 φ ⇝ emb1 ψ) I).
Proof.
  intros [χ Hχ]; apply (unbounded_not_bounded _ (pimp1_unbounded φ ψ)).
  destruct (val1_bounded χ) as [N HN]; exists N.
  intros I HI Hv; exact (HN I HI (proj2 (Hχ I HI) Hv)).
Qed.

Lemma box1_id φ I : Intω I -> (interior (val1 φ) I <-> val1 φ I).
Proof.
  intros HI; apply interior_downset_id; [exact (val1_persistent φ)|unfold Intω in HI; lia].
Qed.

Lemma dia1_not_persistent : ~ ↓ closure (val1 (Var1 1)).
Proof. exact closure_not_downset. Qed.

Section SemanticsProperties.

(** No Top *)
Theorem no_top1 φ : ~ valid1 φ.
Proof.
  intros H.
  pose proof (H (Itv (S (bound1 φ)) (S (bound1 φ))) ltac:(unfold Intω; cbn; lia)) as Hv.
  apply val1_le_bound in Hv; cbn [hi] in Hv; lia.
Qed.

(** No implication *)
Theorem no_imp1 :
  ~ exists imp : form1 -> form1 -> form1,
      forall φ ψ χ, φ ∧ χ ⊨_fs ψ <-> χ ⊨_fs imp φ ψ.
Proof.
  intros [imp Himp].
  assert (H : forall χ, χ ⊨_fs imp ⊥ ⊥)
    by (intros χ; apply Himp; intros I _ [[] _]).
  pose proof (H (Var1 (S (bound1 (imp ⊥ ⊥))))
                (Itv (S (bound1 (imp ⊥ ⊥))) (S (bound1 (imp ⊥ ⊥))))
                ltac:(unfold Intω; cbn; lia) Logic.eq_refl) as Hv.
  apply val1_le_bound in Hv; cbn [hi] in Hv; lia.
Qed.

End SemanticsProperties.

End Semantics.