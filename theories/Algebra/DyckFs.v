(** * Model 1: the paths of finite support ("Logic of Model 1")

  [𝒟_1 = colim_n D_n ≅ 𝒟_fs = {P ∈ 𝒟_ω | |supp(P)| < ∞}]. Of the
  signature [ℒ_ω = {⊥, ⊤, ∧, ∨, →, ¬}] of [𝒟_ω], [𝒟_fs] keeps
  [ℒ_1 = {⊥, ∧, ∨}]: it is a distributive lattice with bottom, without top,
  and therefore without Heyting implication. The logic [ℒ_1] is in
  [ITLfs]. *)

From Stdlib Require Import Arith Bool Lia RelationClasses.
Import Nat.
From Dyck Require Import Lattice Dyck Words DyckOmega.
Import InfinitePath.
Open Scope lattice_scope.

(** ** The set [𝒟_fs] *)

Definition 𝒟_fs : Type := { P : Dyckω | finite (supp P) }.

Definition path_fs (P : 𝒟_fs) : Dyckω := proj1_sig P.
Coercion path_fs : 𝒟_fs >-> Dyckω.

(** The order is that of [𝒟_ω]. *)
#[export] Instance Dyck_fs_Poset : Poset 𝒟_fs.
Proof.
  refine {| po_le (P Q : 𝒟_fs) := leω P Q; po_eq (P Q : 𝒟_fs) := eqω P Q |}.
  - split; [intros P n; lia|].
    intros P Q R H1 H2 n; specialize (H1 n); specialize (H2 n); lia.
  - intros P Q; apply eqω_iff.
Defined.

(** ** The constants: [⊥ ∈ 𝒟_fs], [⊤ ∉ 𝒟_fs] *)

(** [supp(⊥) = ∅]. *)
Lemma udω_finite : finite (supp udω).
Proof. exists 0; intros n Hn; exfalso; apply Hn; reflexivity. Qed.

Definition bot_fs : 𝒟_fs := exist _ udω udω_finite.

#[export] Instance Dyck_fs_Bot : Bot 𝒟_fs :=
  {| bot := bot_fs; le0x := fun P => height_udω_le P |}.

(** [supp(⊤) = ℕ_{≥ 2}] is infinite. *)
Theorem uω_not_fs : ~ finite (supp uω).
Proof. intros H; exact (infinite_not_finite _ uω_infinite H). Qed.

(** ** Closure under [∧] and [∨]

  [supp(P ∧ Q) = supp(P) ∩ supp(Q)] and [supp(P ∨ Q) = supp(P) ∪ supp(Q)]
  are finite with [supp(P)] and [supp(Q)]. *)

Definition meet_fs (P Q : 𝒟_fs) : 𝒟_fs :=
  exist _ (meetω P Q) (finite_supp_meetω P Q (proj2_sig P)).

Definition join_fs (P Q : 𝒟_fs) : 𝒟_fs :=
  exist _ (joinω P Q) (finite_supp_joinω P Q (proj2_sig P) (proj2_sig Q)).

#[export] Instance Dyck_fs_Meet : Meet 𝒟_fs :=
  {| meet := meet_fs; lexI := fun P Q R => lexIω P Q R |}.

#[export] Instance Dyck_fs_Join : Join 𝒟_fs :=
  {| join := join_fs; leUx := fun P Q R => leUxω P Q R |}.

(** [𝒟_fs] is a distributive lattice with bottom. *)
#[export] Instance Dyck_fs_Distributive : Distributive 𝒟_fs.
Proof.
  intros P Q R n.
  change (height (meetω P (joinω Q R)) n = height (joinω (meetω P Q) (meetω P R)) n).
  rewrite h_meetω, !h_joinω, !h_meetω; lia.
Qed.

#[export] Instance Dyck_fs_Lattice : Lattice 𝒟_fs :=
  {| lat_JoinSemilattice := {| jsl_Join := Dyck_fs_Join |};
     lat_MeetSemilattice := {| msl_Meet := Dyck_fs_Meet |} |}.

(** ** No top

  The atom [π_{N+1} = (ud)^N uudd (ud)^ω] has finite support and is at
  height [2] at time [2N + 2]. A path whose support is bounded by [N] is on
  the floor there, so it is not above [π_{N+1}]: no path of finite support
  is above all of them. *)

Definition atom (N : nat) : Dyckω := hills_then N (pyr2_then udω).

Lemma h_atom_peak N : height (atom N) (2 * N + 2) = 2.
Proof.
  unfold atom; rewrite h_hills_then.
  destruct (ltb_spec (2 * N + 2) (2 * N)); [lia|].
  replace (2 * N + 2 - 2 * N) with 2 by lia; apply h_pyr2_then_2.
Qed.

Lemma atom_finite N : finite (supp (atom N)).
Proof.
  exists (2 * N + 4); intros n Hn.
  destruct (lt_ge_cases n (2 * N + 4)) as [Hlt|Hge]; [exact Hlt|exfalso].
  unfold supp, atom in Hn; rewrite h_hills_then, h_udω in Hn.
  destruct (ltb_spec n (2 * N)) as [Hlt|_]; [lia|].
  replace (n - 2 * N) with (S (S (S (S (n - 2 * N - 4))))) in Hn by lia.
  rewrite h_pyr2_then_4, h_udω in Hn; apply Hn.
  replace n with ((n - 2 * N - 4) + 2 * (N + 2)) at 2 by lia.
  rewrite odd_add_mul_2; reflexivity.
Qed.

Definition atom_fs (N : nat) : 𝒟_fs := exist _ (atom N) (atom_finite N).

Theorem no_top_fs : forall T : 𝒟_fs, exists P : 𝒟_fs, ~ P ≤ T.
Proof.
  intros [T [N HN]]; exists (atom_fs N); intros H.
  specialize (H (2 * N + 2)); cbn [atom_fs path_fs proj1_sig] in H.
  rewrite h_atom_peak in H.
  assert (Hs : ~ supp T (2 * N + 2)) by (intros Hs; specialize (HN _ Hs); lia).
  unfold supp in Hs; rewrite h_udω in Hs.
  replace (2 * N + 2) with (0 + 2 * (N + 1)) in Hs by lia.
  rewrite odd_add_mul_2 in Hs; cbn [odd b2n] in Hs.
  destruct (eq_dec (height T (0 + 2 * (N + 1))) 0) as [E|E]; [|contradiction].
  replace (2 * N + 2) with (0 + 2 * (N + 1)) in H by lia; lia.
Qed.

(** ** No Heyting implication

  An implication would make [⊥ → ⊥] a top: every [R] satisfies
  [⊥ ∧ R ≤ ⊥], hence [R ≤ ⊥ → ⊥]. *)
Theorem no_himp_fs :
  ~ exists imp : 𝒟_fs -> 𝒟_fs -> 𝒟_fs, forall P Q R, P ⊓ R ≤ Q <-> R ≤ imp P Q.
Proof.
  intros [imp Himp]; destruct (no_top_fs (imp ⊥ ⊥)) as [P HP].
  apply HP, Himp, leIl.
Qed.
