(** * The logic [ℒ_2] of [𝒟_∞] ("Logic of Model 2") *)

From Stdlib Require Import Arith Lia.
Import Nat.
From Dyck Require Import Interval ITLn ITLω.

Section Syntax.

Inductive form2 : Type :=
| Top2
| Var2 (i : nat)
| Or2 (φ ψ : form2)
| Sup2 (f : nat -> form2).

End Syntax.

Declare Scope form2_scope.
Delimit Scope form2_scope with form2.
Bind Scope form2_scope with form2.
Open Scope form2_scope.

Notation "⊤" := Top2 : form2_scope.
Notation "φ ∨ ψ" := (Or2 φ ψ) (at level 50, left associativity) : form2_scope.
Notation "⋁ f" := (Sup2 f) (at level 35, right associativity) : form2_scope.

Section Semantics.

Fixpoint val2 (φ : form2) (I : interval) : Prop :=
  match φ with
  | ⊤ => True
  | Var2 i => I = Itv i i
  | φ ∨ ψ => val2 φ I \/ val2 ψ I
  | ⋁ f => exists i, val2 (f i) I
  end.

(** [ℒ_2 ⊆ ℒ_ω], with the same truth sets. *)
Fixpoint emb2 (φ : form2) : formω :=
  match φ with
  | ⊤ => ⊤
  | Var2 i => Varω i
  | φ ∨ ψ => emb2 φ ∨ emb2 ψ
  | ⋁ f => ⋁ (fun i => emb2 (f i))
  end.

Lemma valω_emb2 φ : forall I, valω (emb2 φ) I <-> val2 φ I.
Proof.
  induction φ as [|i|φ IHφ ψ IHψ|f IH]; intros I; cbn [emb2 valω val2].
  - reflexivity.
  - reflexivity.
  - split; intros [H|H]; [left; apply IHφ|right; apply IHψ|left; apply IHφ|right; apply IHψ]; assumption.
  - split; intros [i H]; exists i; apply IH; exact H.
Qed.

Lemma val2_persistent φ I J : val2 φ I -> J ⊆ I -> val2 φ J.
Proof.
  intros HI HJ; apply valω_emb2; apply valω_emb2 in HI.
  exact (valω_persistent (emb2 φ) I J HI HJ).
Qed.

(** The formulas of Model 2: those with unbounded truth set. *)
Definition Theta2 (φ : form2) : Prop := unbounded (val2 φ).

(** [⊤ ∈ ℒ_2]. *)
Theorem top2_unbounded : Theta2 ⊤.
Proof.
  intros N; exists (Itv (S N) (S N)).
  split; [unfold Intω; cbn; lia|split; [cbn; lia|exact Logic.I]].
Qed.

(** [∨] keeps Model 2. *)
Theorem or2_unbounded φ ψ : Theta2 φ -> Theta2 (φ ∨ ψ).
Proof.
  intros H N; destruct (H N) as [I [HI [Hh Hv]]].
  exists I; split; [exact HI|split; [exact Hh|left; exact Hv]].
Qed.

(* Formula φ true on odd *)
Definition phiOdd : form2 := ⋁ (fun k => Var2 (2 * k + 1)).
(* Formula φ true on even *)
Definition phiEven : form2 := ⋁ (fun k => Var2 (2 * k + 2)).

Lemma phiOdd_unbounded : Theta2 phiOdd.
Proof.
  intros N; exists (Itv (2 * N + 1) (2 * N + 1)).
  split; [unfold Intω; cbn; lia|split; [cbn; lia|exists N; reflexivity]].
Qed.

Lemma phiEven_unbounded : Theta2 phiEven.
Proof.
  intros N; exists (Itv (2 * N + 2) (2 * N + 2)).
  split; [unfold Intω; cbn; lia|split; [cbn; lia|exists N; reflexivity]].
Qed.

(** [φ_O ∧ φ_E ≡ ⊥]: no interval is both an odd and an even point. So [∧]
  leaves Model 2, as [O ∧ E = ⊥] leaves [𝒟_∞]. *)
Theorem and2_not_closed I : ~ (val2 phiOdd I /\ val2 phiEven I).
Proof.
  intros [[k Hk] [k' Hk']]; cbn in Hk, Hk'; subst I.
  injection Hk' as E1 E2; lia.
Qed.

Definition entails2 (φ ψ : form2) : Prop := forall I, Intω I -> val2 φ I -> val2 ψ I.

Notation "φ ⊨_∞ ψ" := (entails2 φ ψ) (at level 70, no associativity) : form2_scope.

Section SemanticsProperties.

(** [φ_O] and [φ_E] have no lower bound in Model 2: a formula entailing both
  is true nowhere. *)
Theorem no_lower_bound2 :
  ~ exists χ : form2,
      Theta2 χ /\ χ ⊨_∞ phiOdd /\ χ ⊨_∞ phiEven.
Proof.
  intros [χ [Hχ [HO HE]]]; destruct (Hχ 0) as [I [HI [_ Hv]]].
  exact (and2_not_closed I (conj (HO I HI Hv) (HE I HI Hv))).
Qed.

(** No bottom: for [χ] unbounded, hence true on some [I], the formula
  [⋁_k ε_{hi I + 1 + k}], true on the points beyond [I], is unbounded and
  not entailed by [χ]. *)
Definition beyond (N : nat) : form2 := ⋁ (fun k => Var2 (N + 1 + k)).

Lemma beyond_unbounded N : Theta2 (beyond N).
Proof.
  intros M; exists (Itv (N + 1 + M) (N + 1 + M)).
  split; [unfold Intω; cbn; lia|split; [cbn; lia|exists M; reflexivity]].
Qed.

Theorem no_bot2 : forall χ : form2, Theta2 χ ->
  exists ψ : form2, Theta2 ψ /\ ~ χ ⊨_∞ ψ.
Proof.
  intros χ Hχ; destruct (Hχ 0) as [I [HI [_ Hv]]].
  exists (beyond (hi I)); split; [apply beyond_unbounded|].
  intros H; destruct (H I HI Hv) as [k Hk].
  destruct I as [a b]; cbn in Hk; injection Hk as E1 E2; lia.
Qed.

End SemanticsProperties.

End Semantics.
