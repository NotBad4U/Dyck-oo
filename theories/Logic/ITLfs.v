(** * The logic [ℒ_1] of [𝒟_fs] ("Logic of Model 1") *)

From Stdlib Require Import Arith Lia.
Import Nat.
From Dyck Require Import ITLn ITLω.

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

(** [⊤ ∉ ℒ_1]: no formula is true on every interval; it fails on
  [[t_{N+1}, t_{N+1}]] for [N] its bound. *)
Theorem no_top1 φ : ~ validω (val1 φ).
Proof.
  intros H.
  pose proof (H (Itv (S (bound1 φ)) (S (bound1 φ))) ltac:(unfold Intω; cbn; lia)) as Hv.
  apply val1_le_bound in Hv; cbn [hi] in Hv; lia.
Qed.

Definition entails1 (φ ψ : form1) : Prop := forall I, Intω I -> val1 φ I -> val1 ψ I.

End Semantics.

(** [φ ⊨_fs ψ]: on [T_ω], [ψ] is true wherever [φ] is; [fs] as in [𝒟_fs]. *)
Notation "φ ⊨_fs ψ" := (entails1 φ ψ) (at level 70, no associativity) : form1_scope.

Section Entailment.

(** No implication: for any candidate [imp], [⊥ ∧ χ ⊨_fs ⊥] for every [χ], so
  every [χ] would entail [imp ⊥ ⊥]; with [χ = ε_i] this puts [imp ⊥ ⊥] on
  every point, beyond its bound. *)
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

End Entailment.
