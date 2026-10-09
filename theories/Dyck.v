(** * Dyck paths, finite and infinite *)

From Stdlib Require Import Arith Bool Lia.
Import Nat.
Import EqNotations.

Inductive step : Type := U | D. (* U = up step, D = down step *)

Definition step_eq_dec (s t : step) : {s = t} + {s <> t}.
Proof. decide equality. Defined.

(** ** Finite Dyck paths: [D_n]

  The finite Dyck paths are the derivations of the grammar

<<
    P ::= ε | u P d P
>>

*)
Module FinitePath.

(** *** The grammar, indexed by semilength *)

Inductive Dyck : nat -> Type :=
| eps : Dyck 0
| ud {m k : nat} : Dyck m -> Dyck k -> Dyck (S (m + k)). (* [ud A B] is the production [U A D B]. *)

(** [μF = ∐ₙ ℓ⁻¹(n)], and [ℓ] is the first projection. *)
Definition μF := { n : nat & Dyck n }.

(** Specific paths *)

(** hills [(ud)ⁿ] *)
Fixpoint hills n : Dyck n :=
  match n return Dyck n with
  | 0 => eps
  | S n' => ud eps (hills n')
  end.

(** uⁿdⁿ *)
Fixpoint pyramid n : Dyck n :=
  match n return Dyck n with
  | 0 => eps
  | S n' =>
      let fix add_0_r k : k + 0 = k :=
        match k return k + 0 = k with
        | 0 => Logic.eq_refl
        | S k' => f_equal S (add_0_r k')
        end in
      rew [Dyck] f_equal S (add_0_r n') in ud (pyramid n') eps
  end.

(*
  height P i is the height of P after its i-nth steps.
  Equivalently, it is the number of up steps minus the number of down steps
  in the prefix of length i of P i.e. [|{j < i | P_j = u}| - |{j < i | P_j = d}|].
  For a proof that the two are equal, see [height2] in Words.v.
*)
Fixpoint height {n} (P : Dyck n) (i : nat) : nat :=
  match P with
  | eps => 0
  | @ud m _ A B =>
      match i with
      | 0 => 0
      | S j => if j <=? 2 * m then S (height A j) else height B (j - S (2 * m))
      end
  end.

Lemma h_eps i : height eps i = 0.
Proof. reflexivity. Qed.

Lemma h0 {n} (P : Dyck n) : height P 0 = 0.
Proof. now destruct P. Qed.

Lemma hS {m k} (A : Dyck m) (B : Dyck k) j :
  height (ud A B) (S j) = if j <=? 2 * m then S (height A j) else height B (j - S (2 * m)).
Proof. reflexivity. Qed.

Lemma h_cast {m n} (e : m = n) (P : Dyck m) i : height (rew [Dyck] e in P) i = height P i.
Proof. now destruct e. Qed.

(** After its [2n] steps a path stays on the axis. *)
Lemma height_ge {n} (P : Dyck n) i : 2 * n <= i -> height P i = 0.
Proof.
  revert i; induction P as [|m k A IHA B IHB]; intros [|j] Hle; try reflexivity.
  rewrite hS; destruct (leb_spec j (2 * m)); [lia|].
  apply IHB; lia.
Qed.

(** A path climbs at most one level per step, both ways i.e the height can not be greater than `i` axis *)
Lemma height_lei {n} (P : Dyck n) i : height P i <= i.
Proof.
  revert i; induction P as [|m k A IHA B IHB]; intros [|j];
    rewrite ?h_eps, ?h0; try lia.
  rewrite hS; destruct (leb_spec j (2 * m)).
  - specialize (IHA j); lia.
  - specialize (IHB (j - S (2 * m))); lia.
Qed.

Lemma height_le_sub {n} (P : Dyck n) i : height P i <= 2 * n - i.
Proof.
  revert i; induction P as [|m k A IHA B IHB]; intros [|j];
    rewrite ?h_eps, ?h0; try lia.
  rewrite hS; destruct (leb_spec j (2 * m)).
  - specialize (IHA j); lia.
  - specialize (IHB (j - S (2 * m))); lia.
Qed.

Lemma odd_height {n} (P : Dyck n) i : i <= 2 * n -> odd (height P i) = odd i.
Proof.
  revert i; induction P as [|m k A IHA B IHB]; intros [|j] Hle;
    rewrite ?h_eps, ?h0; try reflexivity.
  - exfalso; lia.
  - rewrite hS; destruct (leb_spec j (2 * m)).
    + rewrite !odd_succ, <- !negb_odd, IHA by lia.
      reflexivity.
    + replace (S j) with ((j - S (2 * m)) + 2 * S m) by lia.
      rewrite odd_add_mul_2; apply IHB; lia.
Qed.

(** Along its [2n] steps, [(ud)ⁿ] is at [1] after an odd number of steps and on the axis after an even one. *)
Lemma height_hills n i : i <= 2 * n -> height (hills n) i = if odd i then 1 else 0.
Proof.
  revert i; induction n as [|n IH]; intros [|[|j]] Hle;
    try reflexivity; try (exfalso; lia).
  transitivity (height (hills n) j).
  - simpl; now rewrite sub_0_r.
  - rewrite IH by lia; now rewrite odd_succ, even_succ.
Qed.

Lemma height_pyramid n i : height (pyramid n) i = min i (2 * n - i).
Proof.
  revert i; induction n as [|n IH]; intros [|j]; simpl pyramid;
    rewrite ?h_eps, ?h0; try lia.
  rewrite h_cast, hS; destruct (leb_spec j (2 * n)).
  - rewrite IH; lia.
  - rewrite h_eps; lia.
Qed.

End FinitePath.

(** ** Infinite Dyck paths: [𝒟_ω] and [𝒟_∞]

  An infinite path is an infinite word [P = p₀ p₁ p₂ …] over [{u, d}], i.e.
  a map [nat -> step], and [𝒟_ω] keeps the words that never go below the
  axis. It is a set of words and not of derivations: the grammar read as a
  greatest fixpoint [νF] does flatten onto [𝒟_ω], but not injectively
  (remark following "Dyck initial algebra"), so the two modules do not
  share a representation. Two infinite paths are equal when they take the
  same steps, pointwise; [height_inj] reduces this to equal heights. *)

Module InfinitePath.

(** *** The set [𝒟_ω] *)

(** [nU P n = |{i < n | p_i = u}|] and [nD P n = |{i < n | p_i = d}|]. *)
Fixpoint nU (P : nat -> step) (n : nat) : nat :=
  match n with
  | 0 => 0
  | S i => nU P i + match P i with U => 1 | D => 0 end
  end.

Fixpoint nD (P : nat -> step) (n : nat) : nat :=
  match n with
  | 0 => 0
  | S i => nD P i + match P i with U => 0 | D => 1 end
  end.

(** [𝒟_ω = {P ∈ {u, d}^ω | ∀ n, h_P(n) ≥ 0}]. In [nat] the condition
  [h_P(n) ≥ 0] reads [|{i < n | p_i = d}| ≤ |{i < n | p_i = u}|]. Through
  the coercion [steps], [P i] is the step [p_i]. *)
Record Dyckω : Type := mkDyckω {
  steps :> nat -> step;
  steps_nonneg : forall n, nD steps n <= nU steps n
}.

(** [h_P(n) = |{i < n | p_i = u}| - |{i < n | p_i = d}|], exact in [nat] by
  [steps_nonneg]. *)
Definition height (P : Dyckω) (n : nat) : nat := nU P n - nD P n.

Lemma height_0 (P : Dyckω) : height P 0 = 0.
Proof. reflexivity. Qed.

(** A step [u] climbs one level and a step [d] goes down one level; in
  particular no step [d] starts on the axis. *)
Lemma height_up (P : Dyckω) n : P n = U -> height P (S n) = S (height P n).
Proof.
  intros E; pose proof (steps_nonneg P n).
  unfold height; cbn [nU nD]; rewrite E; cbn [nU nD]; lia.
Qed.

Lemma height_down (P : Dyckω) n : P n = D -> S (height P (S n)) = height P n.
Proof.
  intros E; pose proof (steps_nonneg P (S n)) as H.
  unfold height in *; cbn [nU nD] in *; rewrite E in *; cbn [nU nD] in *; lia.
Qed.

Lemma height_step (P : Dyckω) n : height P (S n) = S (height P n) \/ S (height P (S n)) = height P n.
Proof.
  destruct (P n) eqn:E; [left; apply height_up|right; apply height_down]; exact E.
Qed.

Lemma height_lei (P : Dyckω) n : height P n <= n.
Proof.
  induction n as [|n IH]; [rewrite height_0; lia|].
  destruct (height_step P n); lia.
Qed.

(** The height after [n] steps has the parity of [n]. *)
Lemma odd_height (P : Dyckω) n : odd (height P n) = odd n.
Proof.
  induction n as [|n IH]; [rewrite height_0; reflexivity|].
  destruct (P n) eqn:E.
  - rewrite (height_up P n E), !odd_succ, <- !negb_odd, IH; reflexivity.
  - rewrite <- (height_down P n E), odd_succ in IH.
    rewrite odd_succ, <- negb_even, IH, negb_odd; reflexivity.
Qed.

(** A path is determined by its heights. *)
Lemma height_inj (P Q : Dyckω) : (forall n, height P n = height Q n) -> forall n, P n = Q n.
Proof.
  intros E n; pose proof (E n); pose proof (E (S n)).
  destruct (P n) eqn:EP, (Q n) eqn:EQ; try reflexivity.
  - pose proof (height_up P n EP); pose proof (height_down Q n EQ); lia.
  - pose proof (height_down P n EP); pose proof (height_up Q n EQ); lia.
Qed.

(** *** The paths [⊥ = (ud)^ω] and [⊤ = u^ω] *)

(** [⊥ = (ud)^ω], the path all of whose factors are hills: [p_i = u] at
  even [i] and [p_i = d] at odd [i]. *)
Definition ud_steps (i : nat) : step := if odd i then D else U.

Lemma ud_count n : nD ud_steps n + b2n (odd n) = nU ud_steps n.
Proof.
  induction n as [|n IH]; [reflexivity|].
  cbn [nU nD]; unfold ud_steps in *.
  rewrite odd_succ, <- negb_odd.
  destruct (odd n); cbn [negb b2n] in *; lia.
Qed.

Lemma ud_nonneg n : nD ud_steps n <= nU ud_steps n.
Proof. rewrite <- ud_count; lia. Qed.

Definition udω : Dyckω := mkDyckω ud_steps ud_nonneg.

Lemma h_udω n : height udω n = b2n (odd n).
Proof.
  unfold height; change (steps udω) with ud_steps.
  rewrite <- (ud_count n); lia.
Qed.

(** [⊤ = u^ω], which never comes back to the axis. *)
Lemma nU_u n : nU (fun _ => U) n = n.
Proof. induction n as [|n IH]; cbn [nU]; lia. Qed.

Lemma nD_u n : nD (fun _ => U) n = 0.
Proof. induction n as [|n IH]; cbn [nD]; lia. Qed.

Lemma u_nonneg n : nD (fun _ => U) n <= nU (fun _ => U) n.
Proof. rewrite nU_u, nD_u; lia. Qed.

Definition uω : Dyckω := mkDyckω (fun _ => U) u_nonneg.

Lemma h_uω n : height uω n = n.
Proof.
  unfold height; change (steps uω) with (fun _ : nat => U).
  rewrite nU_u, nD_u; lia.
Qed.

(** Every path lies between [⊥] and [⊤], height by height. *)
Lemma height_udω_le (P : Dyckω) n : height udω n <= height P n.
Proof.
  rewrite h_udω; pose proof (odd_height P n) as Ho.
  destruct (odd n); cbn [b2n]; [|lia].
  destruct (height P n); [discriminate Ho|lia].
Qed.

Lemma height_le_uω (P : Dyckω) n : height P n <= height uω n.
Proof. rewrite h_uω; apply height_lei. Qed.

(** *** Support

  [supp(P) = {n | h_P(n) ≠ h_⊥(n)}] collects the times at which [P] is not
  where [⊥] is, and [supp_at(P) = {i ≥ 1 | h_P(2i) > 0}] samples the even
  times only. Both are predicates on [nat]. *)

Definition supp (P : Dyckω) (n : nat) : Prop := height P n <> height udω n.

Definition supp_at (P : Dyckω) (i : nat) : Prop := 1 <= i /\ 0 < height P (2 * i).

(** A subset of [ℕ] is finite when it is bounded, and infinite when it is
  unbounded, i.e. it has elements beyond every bound. Each is classically
  the negation of the other; the positive forms are the ones stated. *)
Definition finite (A : nat -> Prop) : Prop := exists N, forall n, A n -> n < N.

Definition infinite (A : nat -> Prop) : Prop := forall N, exists n, N <= n /\ A n.

(** Lemma of "Ambient definitions": [supp_at(P) = {i | 2i ∈ supp(P)}]. *)
Lemma supp_at_iff (P : Dyckω) i : supp_at P i <-> supp P (2 * i).
Proof.
  unfold supp_at, supp; rewrite h_udω.
  assert (E : odd (2 * i) = false) by (rewrite odd_mul; reflexivity).
  rewrite E; cbn [b2n]; split; [lia|intros H; split; [|lia]].
  destruct i as [|i]; [exfalso; apply H; reflexivity|lia].
Qed.

(** A time [n] of the support has its half in [supp_at]: at an odd [n]
  the height is odd and is not [1], so it is at least [2], and the height
  one step earlier is positive. *)
Lemma supp_div2 (P : Dyckω) n : supp P n -> supp_at P (div2 n).
Proof.
  unfold supp, supp_at; rewrite h_udω; intros H.
  pose proof (div2_odd n) as En; pose proof (odd_height P n) as Ho.
  remember (div2 n) as i eqn:Ei; clear Ei.
  destruct (odd n); cbn [b2n] in H, En; subst n.
  - rewrite add_1_r in *.
    assert (height P (S (2 * i)) <> 0) by (intros E; rewrite E in Ho; discriminate Ho).
    pose proof (height_lei P (S (2 * i))); destruct (height_step P (2 * i)); lia.
  - rewrite add_0_r in *; pose proof (height_lei P (2 * i)); lia.
Qed.

(** Lemma of "Ambient definitions":
  [|supp(P)| < ∞ ⟺ |supp_at(P)| < ∞]. *)
Lemma finite_supp_iff (P : Dyckω) : finite (supp P) <-> finite (supp_at P).
Proof.
  split; intros [N HN].
  - exists N; intros i Hi; apply supp_at_iff in Hi; specialize (HN _ Hi); lia.
  - exists (S (2 * N)); intros n Hn.
    specialize (HN _ (supp_div2 P n Hn)); pose proof (div2_odd n).
    destruct (odd n); cbn [b2n] in *; lia.
Qed.

(** The same lemma, in the form used by [𝒟_∞]. *)
Lemma infinite_supp_iff (P : Dyckω) : infinite (supp P) <-> infinite (supp_at P).
Proof.
  split; intros H N.
  - destruct (H (2 * N)) as [n [Hn Hs]].
    exists (div2 n); split; [|exact (supp_div2 P n Hs)].
    pose proof (div2_odd n); destruct (odd n); cbn [b2n] in *; lia.
  - destruct (H N) as [i [Hi Hs]].
    exists (2 * i); split; [lia|apply supp_at_iff, Hs].
Qed.

(** *** The set [𝒟_∞]

  [𝒟_∞ = {P ∈ 𝒟_ω | |supp(P)| = ∞}], the paths of infinite support of
  Model 2: those that keep leaving the floor [⊥] arbitrarily late. *)

Definition Dyck_inf : Type := { P : Dyckω | infinite (supp P) }.

(** [⊤ ∈ 𝒟_∞] (section "Model 2"): [supp(⊤) = ℕ_{≥ 2}]. *)
Lemma uω_infinite : infinite (supp uω).
Proof.
  intros N; exists (N + 2); split; [lia|].
  unfold supp; rewrite h_uω, h_udω.
  destruct (odd (N + 2)); cbn [b2n]; lia.
Qed.

(** [⊥ ∉ 𝒟_∞]: its support is empty. *)
Lemma udω_not_infinite : ~ infinite (supp udω).
Proof. intros H; destruct (H 0) as [n [_ Hn]]; apply Hn; reflexivity. Qed.

End InfinitePath.
