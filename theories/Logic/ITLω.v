(** * The logic [ℒ_ω] of [𝒟_ω] ("Unbounded Interval Temporal Logics")

  The interval semantics of [ITLn] on the unbounded time line [T_ω = {t_1, t_2, … t_ω}] and
  the intervals are the [[t_i, t_j]] with [1 ≤ i ≤ j].
*)

From Stdlib Require Import Arith Lia.
Import Nat.
From Dyck Require Import ITLn.

Section Syntax.

Inductive formω : Type :=
| Botω
| Topω
| Varω (i : nat)                 (* [ε_i], true exactly on [[t_i, t_i]] *)
| Andω (φ ψ : formω)
| Orω (φ ψ : formω)
| Pimpω (φ ψ : formω)            (* [φ ⇝ ψ] *)
| Pnegω (φ : formω)              (* [∼ φ] *)
| Supω (f : nat -> formω)        (* [⋁_i f i] *)
| Infω (f : nat -> formω).       (* [⋀_i f i] *)

End Syntax.


Declare Scope formω_scope.
Delimit Scope formω_scope with formω.
Bind Scope formω_scope with formω.
Open Scope formω_scope.

Notation "⊥" := Botω : formω_scope.
Notation "⊤" := Topω : formω_scope.
Notation "φ ∨ ψ" := (Orω φ ψ) (at level 50, left associativity) : formω_scope.
Notation "φ ∧ ψ" := (Andω φ ψ) (at level 40, left associativity) : formω_scope.
Notation "φ ⇝ ψ" := (Pimpω φ ψ) (at level 60, right associativity) : formω_scope.
Notation "∼ φ" := (Pnegω φ) (at level 35, right associativity) : formω_scope.
Notation "⋁ f" := (Supω f) (at level 35, right associativity) : formω_scope.
Notation "⋀ f" := (Infω f) (at level 35, right associativity) : formω_scope.

Section Semantics.

Fixpoint valω (φ : formω) (I : interval) : Prop :=
  match φ with
  | ⊥ => False
  | ⊤ => True
  | Varω i => I = Itv i i
  | φ ∧ ψ => valω φ I /\ valω ψ I
  | φ ∨ ψ => valω φ I \/ valω ψ I
  | φ ⇝ ψ => forall J, J ⊆ I -> valω φ J -> valω ψ J
  | ∼ φ => forall J, J ⊆ I -> ~ valω φ J
  | ⋁ f => exists i, valω (f i) I
  | ⋀ f => forall i, valω (f i) I
  end.

Definition persistent (φ : formω) : Prop := forall I J, valω φ I -> J ⊆ I -> valω φ J.

Theorem valω_persistent φ : persistent φ.
Proof.
  induction φ as [| |i|φ IHφ ψ IHψ|φ IHφ ψ IHψ|φ IHφ ψ IHψ|φ IHφ|f IH|f IH];
    intros I J HI HJ; cbn [valω] in *.
  - exact HI.
  - exact HI.
  - subst I; exact (sub_point J i HJ).
  - destruct HI as [H1 H2]; split; [exact (IHφ I J H1 HJ)|exact (IHψ I J H2 HJ)].
  - destruct HI as [H|H]; [left; exact (IHφ I J H HJ)|right; exact (IHψ I J H HJ)].
  - intros K HK; exact (HI K (sub_trans K J I HK HJ)).
  - intros K HK; exact (HI K (sub_trans K J I HK HJ)).
  - destruct HI as [i H]; exists i; exact (IH i I J H HJ).
  - intros i; exact (IH i I J (HI i) HJ).
Qed.

(** [Intω I]: [I] is an interval of [T_ω]. *)
Definition Intω (I : interval) : Prop := 1 <= lo I /\ lo I <= hi I.

Definition entailsω (φ ψ : formω) : Prop := forall I, Intω I -> valω φ I -> valω ψ I.

Notation "φ ⊨_ω ψ" := (entailsω φ ψ) (at level 70, no associativity) : formω_scope.

(** [⇝] is the adjoint for [∧] *)
Lemma pimpω_adj φ ψ χ :
  φ ∧ χ ⊨_ω ψ <-> χ ⊨_ω φ ⇝ ψ.
Proof.
  split.
  - intros H I HI Hχ J HJ Hφ.
    apply (H J); [unfold Intω, sub in *; lia|].
    split; [exact Hφ|exact (valω_persistent χ I J Hχ HJ)].
  - intros H I HI [Hφ Hχ]; apply (H I HI Hχ I); [unfold Intω, sub in *; lia|exact Hφ].
Qed.

Lemma supω_lub f ψ : (forall i, f i ⊨_ω ψ) <-> ⋁ f ⊨_ω ψ.
Proof.
  split.
  - intros H I HI [i Hi]; exact (H i I HI Hi).
  - intros H i I HI Hi; apply (H I HI); exists i; exact Hi.
Qed.

Lemma infω_glb f χ : (forall i, χ ⊨_ω f i) <-> χ ⊨_ω ⋀ f.
Proof.
  split.
  - intros H I HI Hu i; exact (H i I HI Hu).
  - intros H i I HI Hu; exact (H I HI Hu i).
Qed.

End Semantics.
