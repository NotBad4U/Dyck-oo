(** * Model 2: the paths of infinite support ("Logic of Model 2")

  [𝒟_2 = 𝒟_is = 𝒟_∞ = {P ∈ 𝒟_ω | |supp(P)| = ∞}], defined in [Dyck]. Of
  the signature [ℒ_ω = {⊥, ⊤, ∧, ∨, →, ¬}] of [𝒟_ω], [𝒟_∞] keeps
  [ℒ_2 = {⊤, ∨}]: it is a join-semilattice with top. It has no bottom, and
  [∧] does not stay in it: the two paths [O = (uudd)^ω] and
  [E = ud (uudd)^ω] of the paper have disjoint supports, so [O ∧ E = ⊥];
  they have no lower bound at all in [𝒟_∞]. Implication and negation
  presuppose [∧] and [⊥], so they are not available either. The logic [ℒ_2] is in
  [ITLinf]. *)

From Stdlib Require Import Arith Bool Lia RelationClasses.
Import Nat.
From Dyck Require Import Lattice Dyck Words DyckOmega.
Import InfinitePath.
Open Scope lattice_scope.

(** ** The set [𝒟_∞] *)

Definition path_inf (P : 𝒟_∞) : Dyckω := proj1_sig P.
Coercion path_inf : Dyck_inf >-> Dyckω.

(** The order is that of [𝒟_ω]. *)
#[export] Instance Dyck_inf_Poset : Poset 𝒟_∞.
Proof.
  refine {| po_le (P Q : 𝒟_∞) := leω P Q; po_eq (P Q : 𝒟_∞) := eqω P Q |}.
  - split; [intros P n; lia|].
    intros P Q R H1 H2 n; specialize (H1 n); specialize (H2 n); lia.
  - intros P Q; apply eqω_iff.
Defined.

(** ** The constants: [⊤ ∈ 𝒟_∞], [⊥ ∉ 𝒟_∞] ([uω_infinite], [udω_not_infinite]) *)

Definition top_inf : 𝒟_∞ := exist _ uω uω_infinite.

#[export] Instance Dyck_inf_Top : Top 𝒟_∞ :=
  {| top := top_inf; lex1 := fun P => height_le_uω P |}.

(** ** Closure under [∨]

  [supp(P ∨ Q) = supp(P) ∪ supp(Q)] is infinite as soon as [supp(P)] is. *)

Definition join_inf (P Q : 𝒟_∞) : 𝒟_∞ :=
  exist _ (joinω P Q) (infinite_supp_joinω P Q (proj2_sig P)).

(** [𝒟_∞] is a join-semilattice with top. *)
#[export] Instance Dyck_inf_Join : Join 𝒟_∞ :=
  {| join := join_inf; leUx := fun P Q R => leUxω P Q R |}.

(** ** [∧] is not closed: [O = (uudd)^ω] and [E = ud (uudd)^ω]

  [O] is given stage by stage, [O_{n+2} = ud (ud ε ε) O_n], and [E = ud · O].
  Their heights are [4]-periodic: [h_O] runs [0 1 2 1], [h_E] runs
  [0 1 0 1 2 1] then [0 1 2 1]. *)

Fixpoint O_stage (n : nat) : FinitePath.Dyck n :=
  match n with
  | 0 => FinitePath.eps
  | 1 => FinitePath.ud FinitePath.eps FinitePath.eps
  | S (S k) => FinitePath.ud (FinitePath.ud FinitePath.eps FinitePath.eps) (O_stage k)
  end.

Lemma O_stage_coherent : forall n i, i <= n ->
  FinitePath.height (O_stage (S n)) i = FinitePath.height (O_stage n) i.
Proof.
  induction n as [n IH] using (well_founded_ind lt_wf_0); intros i Hi.
  destruct n as [|[|k]].
  - replace i with 0 by lia; rewrite !FinitePath.h0; reflexivity.
  - destruct i as [|[|j]]; [reflexivity|reflexivity|lia].
  - destruct i as [|j]; [rewrite !FinitePath.h0; reflexivity|].
    cbn [O_stage FinitePath.height].
    destruct (leb_spec j (2 * S (0 + 0))); [reflexivity|apply IH; lia].
Qed.

Definition O : Dyckω := mkDyckω O_stage O_stage_coherent.

Definition E : Dyckω := hill_then O.

(** [h_O], as a [4]-periodic function. *)
Fixpoint hO (n : nat) : nat :=
  match n with
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 1
  | S (S (S (S m))) => hO m
  end.

Lemma h_O n : height O n = hO n.
Proof.
  induction n as [n IH] using (well_founded_ind lt_wf_0).
  destruct n as [|[|[|[|m]]]]; [reflexivity|reflexivity|reflexivity|reflexivity|].
  unfold height at 1.
  change (O (S (S (S (S m))))) with
    (FinitePath.ud (FinitePath.ud FinitePath.eps FinitePath.eps) (O (S (S m)))).
  cbn [FinitePath.height].
  destruct (leb_spec (S (S (S m))) (2 * S (0 + 0))); [lia|].
  replace (S (S (S m)) - S (2 * S (0 + 0))) with m by lia.
  rewrite height_stage by lia; cbn [hO]; apply IH; lia.
Qed.

Lemma hO_4 m : hO (S (S (S (S m)))) = hO m.
Proof. reflexivity. Qed.

Lemma hO_peak q : hO (4 * q + 2) = 2.
Proof.
  induction q as [|q IH]; [reflexivity|].
  replace (4 * S q + 2) with (S (S (S (S (4 * q + 2))))) by lia.
  rewrite hO_4; exact IH.
Qed.

(** The two periodic patterns never both leave the floor: [min] of [h_O]
  and of [h_O] shifted by two is [h_⊥]. *)
Lemma hO_min m : min (hO (S (S m))) (hO m) = b2n (odd m).
Proof.
  induction m as [m IH] using (well_founded_ind lt_wf_0).
  destruct m as [|[|[|[|m]]]]; [reflexivity|reflexivity|reflexivity|reflexivity|].
  change (hO (S (S (S (S (S (S m))))))) with (hO (S (S m))); rewrite hO_4.
  rewrite IH by lia.
  replace (S (S (S (S m)))) with (m + 2 * 2) by lia; rewrite odd_add_mul_2; reflexivity.
Qed.

(** [O, E ∈ 𝒟_∞]: [supp(O) ⊇ 4ℕ + 2] and [supp(E) ⊇ 4ℕ + 4]. *)
Lemma O_infinite : infinite (supp O).
Proof.
  intros N; exists (4 * N + 2); split; [lia|].
  unfold supp; rewrite h_O, hO_peak, h_udω.
  replace (4 * N + 2) with (0 + 2 * (2 * N + 1)) by lia; rewrite odd_add_mul_2.
  cbn; lia.
Qed.

Lemma E_infinite : infinite (supp E).
Proof.
  intros N; exists (S (S (4 * N + 2))); split; [lia|].
  unfold supp, E; rewrite h_hill_then_2, h_O, hO_peak, h_udω.
  replace (S (S (4 * N + 2))) with (0 + 2 * (2 * N + 2)) by lia; rewrite odd_add_mul_2.
  cbn; lia.
Qed.

Definition O_inf : 𝒟_∞ := exist _ O O_infinite.
Definition E_inf : 𝒟_∞ := exist _ E E_infinite.

(** [O ∧ E = ⊥], height by height. *)
Lemma h_meet_O_E n : height (meetω O E) n = height udω n.
Proof.
  rewrite h_meetω, h_udω; destruct n as [|[|m]]; [reflexivity|reflexivity|].
  unfold E; rewrite h_hill_then_2, !h_O, hO_min, odd_succ_succ; reflexivity.
Qed.

(** So [∧] leaves [𝒟_∞]: [supp(O ∧ E) = ∅]. *)
Theorem meet_not_closed : ~ infinite (supp (meetω O E)).
Proof.
  intros H; apply udω_not_infinite.
  apply (infinite_ext (supp (meetω O E))); [|exact H].
  intros n; unfold supp; rewrite h_meet_O_E; reflexivity.
Qed.

(** Worse, [O] and [E] have no lower bound in [𝒟_∞] at all, so [𝒟_∞] has no
  meet: a lower bound is below [O ∧ E = ⊥], hence has empty support. *)
Theorem no_lower_bound : ~ exists R : 𝒟_∞, R ≤ O_inf /\ R ≤ E_inf.
Proof.
  intros [[R HR] [H1 H2]]; apply (infinite_not_finite _ HR).
  exists 0; intros n Hn; exfalso.
  unfold supp in Hn; specialize (H1 n); specialize (H2 n); cbn [path_inf proj1_sig O_inf E_inf] in H1, H2.
  pose proof (h_meet_O_E n) as H; rewrite h_meetω in H.
  pose proof (height_udω_le R n); lia.
Qed.

(** ** No bottom

  [(ud)^m u^ω ∈ 𝒟_∞] stays on the floor until time [2m]. A path [B] of
  infinite support leaves the floor at some time [n]; it is not below
  [(ud)^n u^ω] there, so no path of [𝒟_∞] is below all of them. *)

Lemma hills_uω_infinite m : infinite (supp (hills_then m uω)).
Proof.
  intros N; exists (2 * m + N + 2); split; [lia|].
  unfold supp; rewrite h_hills_then, h_uω, h_udω.
  destruct (ltb_spec (2 * m + N + 2) (2 * m)); [lia|].
  destruct (odd (2 * m + N + 2)); cbn [b2n]; lia.
Qed.

Theorem no_bot_inf : forall B : 𝒟_∞, exists Q : 𝒟_∞, ~ B ≤ Q.
Proof.
  intros [B HB]; destruct (HB 0) as [n [_ Hn]].
  exists (exist _ (hills_then n uω) (hills_uω_infinite n)); intros H.
  specialize (H n); cbn [path_inf proj1_sig] in H.
  rewrite h_hills_then in H; unfold supp in Hn; rewrite h_udω in Hn.
  destruct (ltb_spec n (2 * n)) as [_|Hn0].
  - pose proof (height_udω_le B n); rewrite h_udω in *; lia.
  - assert (n = 0) by lia; subst n; rewrite height_0 in Hn; apply Hn; reflexivity.
Qed.
