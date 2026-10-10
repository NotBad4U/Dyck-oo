(** * The lattice [𝒟_ω]

  The geometric order on infinite paths, with meet and join computed stage
  by stage from those of the [D_n] ([meetD], [joinD] of [Words]). This is
  the part of "Completion" that both models share: [DyckFs] and [DyckInf]
  each keep the operations that stay inside their subset of [𝒟_ω]. The
  logic [ℒ_ω] is in [ITLω]. *)

From Stdlib Require Import Arith Bool Lia RelationClasses.
Import Nat.
From Dyck Require Import Lattice Dyck Words.
Import InfinitePath.
Open Scope lattice_scope.

(** ** The geometric order

  [P ≤ Q] when [h_P(n) ≤ h_Q(n)] at every time [n]. Two paths are equal
  when they have the same heights: the stages beyond the prefix they fix
  are not part of the path. *)

Definition leω (P Q : Dyckω) : Prop := forall n, height P n <= height Q n.

Definition eqω (P Q : Dyckω) : Prop := forall n, height P n = height Q n.

Lemma eqω_iff P Q : eqω P Q <-> leω P Q /\ leω Q P.
Proof.
  split; [intros E; split; intros n; rewrite (E n); lia|].
  intros [H1 H2] n; specialize (H1 n); specialize (H2 n); lia.
Qed.

#[export] Instance leω_PreOrder : PreOrder leω.
Proof.
  split; [intros P n; lia|].
  intros P Q R H1 H2 n; specialize (H1 n); specialize (H2 n); lia.
Qed.

#[export] Instance Dyckω_Poset : Poset Dyckω :=
  {| po_le := leω; po_eq := eqω; po_le_PreOrder := leω_PreOrder; po_eqE := eqω_iff |}.

(** ** Meet and join, stage by stage

  [h_{P ∧ Q} = min(h_P, h_Q)] and [h_{P ∨ Q} = max(h_P, h_Q)]. The stage [n]
  of [P ∧ Q] is [P_n ∧ Q_n] in [D_n]; it is coherent because [meetD] is
  pointwise on heights. *)

Definition meetω (P Q : Dyckω) : Dyckω.
Proof.
  refine (mkDyckω (fun n => meetD (P n) (Q n)) _).
  intros n i Hi; rewrite !h_meetD, (coherent P n i Hi), (coherent Q n i Hi); reflexivity.
Defined.

Definition joinω (P Q : Dyckω) : Dyckω.
Proof.
  refine (mkDyckω (fun n => joinD (P n) (Q n)) _).
  intros n i Hi; rewrite !h_joinD, (coherent P n i Hi), (coherent Q n i Hi); reflexivity.
Defined.

Lemma h_meetω P Q n : height (meetω P Q) n = min (height P n) (height Q n).
Proof. exact (h_meetD (P n) (Q n) n). Qed.

Lemma h_joinω P Q n : height (joinω P Q) n = max (height P n) (height Q n).
Proof. exact (h_joinD (P n) (Q n) n). Qed.

Lemma lexIω P Q R : leω R (meetω P Q) <-> leω R P /\ leω R Q.
Proof.
  split.
  - intros H; split; intros n; specialize (H n); rewrite h_meetω in H; lia.
  - intros [H1 H2] n; rewrite h_meetω; specialize (H1 n); specialize (H2 n); lia.
Qed.

Lemma leUxω P Q R : leω (joinω P Q) R <-> leω P R /\ leω Q R.
Proof.
  split.
  - intros H; split; intros n; specialize (H n); rewrite h_joinω in H; lia.
  - intros [H1 H2] n; rewrite h_joinω; specialize (H1 n); specialize (H2 n); lia.
Qed.

#[export] Instance Dyckω_Meet : Meet Dyckω := {| meet := meetω; lexI := lexIω |}.

#[export] Instance Dyckω_Join : Join Dyckω := {| join := joinω; leUx := leUxω |}.

#[export] Instance Dyckω_Bot : Bot Dyckω := {| bot := udω; le0x := height_udω_le |}.

#[export] Instance Dyckω_Top : Top Dyckω := {| top := uω; lex1 := height_le_uω |}.

#[export] Instance Dyckω_Distributive : Distributive Dyckω.
Proof.
  intros P Q R n.
  change (height (meetω P (joinω Q R)) n = height (joinω (meetω P Q) (meetω P R)) n).
  rewrite h_meetω, !h_joinω, !h_meetω; lia.
Qed.

(** ** Support of a meet and of a join

  Since [⊥ ≤ P], [n ∈ supp(P)] means [h_P(n) > h_⊥(n)]; hence
  [supp(P ∧ Q) = supp(P) ∩ supp(Q)] and [supp(P ∨ Q) = supp(P) ∪ supp(Q)]
  ("Logic of Model 1" and "Logic of Model 2"). *)

Lemma supp_gt P n : supp P n <-> height udω n < height P n.
Proof. unfold supp; pose proof (height_udω_le P n) as Hb; split; intros H; lia. Qed.

Lemma supp_meetω P Q n : supp (meetω P Q) n <-> supp P n /\ supp Q n.
Proof.
  rewrite !supp_gt, h_meetω; split; [intros H; split; lia|intros [H1 H2]; lia].
Qed.

Lemma supp_joinω P Q n : supp (joinω P Q) n <-> supp P n \/ supp Q n.
Proof. rewrite !supp_gt, h_joinω; split; [intros H; lia|intros [H|H]; lia]. Qed.

(** *** Finite and infinite subsets of [ℕ] *)

Lemma finite_ext (A B : nat -> Prop) : (forall n, A n <-> B n) -> finite A -> finite B.
Proof. intros E [N HN]; exists N; intros n Hn; apply HN, E, Hn. Qed.

Lemma infinite_ext (A B : nat -> Prop) : (forall n, A n <-> B n) -> infinite A -> infinite B.
Proof.
  intros E H N; destruct (H N) as [n [Hn HA]]; exists n; split; [exact Hn|apply E, HA].
Qed.

Lemma finite_inter_l (A B : nat -> Prop) : finite A -> finite (fun n => A n /\ B n).
Proof. intros [N HN]; exists N; intros n [Hn _]; apply HN, Hn. Qed.

Lemma finite_union (A B : nat -> Prop) : finite A -> finite B -> finite (fun n => A n \/ B n).
Proof.
  intros [N HN] [M HM]; exists (max N M); intros n [Hn|Hn];
    [specialize (HN n Hn)|specialize (HM n Hn)]; lia.
Qed.

Lemma infinite_union_l (A B : nat -> Prop) : infinite A -> infinite (fun n => A n \/ B n).
Proof.
  intros H N; destruct (H N) as [n [Hn HA]]; exists n; split; [exact Hn|left; exact HA].
Qed.

Lemma infinite_not_finite (A : nat -> Prop) : infinite A -> finite A -> False.
Proof. intros H [N HN]; destruct (H N) as [n [Hn HA]]; specialize (HN n HA); lia. Qed.

Lemma finite_supp_meetω P Q : finite (supp P) -> finite (supp (meetω P Q)).
Proof.
  intros H; apply (finite_ext (fun n => supp P n /\ supp Q n)).
  - intros n; symmetry; apply supp_meetω.
  - apply finite_inter_l, H.
Qed.

Lemma finite_supp_joinω P Q : finite (supp P) -> finite (supp Q) -> finite (supp (joinω P Q)).
Proof.
  intros HP HQ; apply (finite_ext (fun n => supp P n \/ supp Q n)).
  - intros n; symmetry; apply supp_joinω.
  - apply finite_union; assumption.
Qed.

Lemma infinite_supp_joinω P Q : infinite (supp P) -> infinite (supp (joinω P Q)).
Proof.
  intros H; apply (infinite_ext (fun n => supp P n \/ supp Q n)).
  - intros n; symmetry; apply supp_joinω.
  - apply infinite_union_l, H.
Qed.

(** ** Prepending a factor

  [hill_then P = ud · P] and [pyr2_then P = uudd · P], stage by stage: the
  stage [n] of [ud · P] is [ud ε P_{n-1}], the stage [n + 2] of [uudd · P]
  is [ud (ud ε ε) P_n]. The indices work out without casts. These build the
  witnesses of the two models: the atoms [(ud)^k uudd (ud)^ω] and the paths
  [(ud)^k u^ω]. *)

Definition hill_stage (P : Dyckω) (n : nat) : FinitePath.Dyck n :=
  match n with
  | 0 => FinitePath.eps
  | S k => FinitePath.ud FinitePath.eps (P k)
  end.

Lemma hill_stage_coherent P n i : i <= n ->
  FinitePath.height (hill_stage P (S n)) i = FinitePath.height (hill_stage P n) i.
Proof.
  intros Hi; destruct n as [|k].
  - replace i with 0 by lia; rewrite !FinitePath.h0; reflexivity.
  - destruct i as [|j]; [rewrite !FinitePath.h0; reflexivity|].
    cbn [hill_stage FinitePath.height].
    destruct (leb_spec j (2 * 0)); [reflexivity|apply coherent; lia].
Qed.

Definition hill_then (P : Dyckω) : Dyckω := mkDyckω (hill_stage P) (hill_stage_coherent P).

Lemma h_hill_then_0 P : height (hill_then P) 0 = 0.
Proof. apply height_0. Qed.

Lemma h_hill_then_1 P : height (hill_then P) 1 = 1.
Proof. reflexivity. Qed.

Lemma h_hill_then_2 P m : height (hill_then P) (S (S m)) = height P m.
Proof.
  unfold height; cbn [stage hill_then hill_stage FinitePath.height].
  destruct (leb_spec (S m) (2 * 0)); [lia|].
  replace (S m - S (2 * 0)) with m by lia.
  change (FinitePath.height (P m) m) with (height P m); apply height_stage; lia.
Qed.

Definition pyr2_stage (P : Dyckω) (n : nat) : FinitePath.Dyck n :=
  match n with
  | 0 => FinitePath.eps
  | 1 => FinitePath.ud FinitePath.eps FinitePath.eps
  | S (S k) => FinitePath.ud (FinitePath.ud FinitePath.eps FinitePath.eps) (P k)
  end.

Lemma pyr2_stage_coherent P n i : i <= n ->
  FinitePath.height (pyr2_stage P (S n)) i = FinitePath.height (pyr2_stage P n) i.
Proof.
  intros Hi; destruct n as [|[|k]].
  - replace i with 0 by lia; rewrite !FinitePath.h0; reflexivity.
  - destruct i as [|[|j]]; [reflexivity|reflexivity|lia].
  - destruct i as [|j]; [rewrite !FinitePath.h0; reflexivity|].
    cbn [pyr2_stage FinitePath.height].
    destruct (leb_spec j (2 * S (0 + 0))); [reflexivity|apply coherent; lia].
Qed.

Definition pyr2_then (P : Dyckω) : Dyckω := mkDyckω (pyr2_stage P) (pyr2_stage_coherent P).

Lemma h_pyr2_then_1 P : height (pyr2_then P) 1 = 1.
Proof. reflexivity. Qed.

Lemma h_pyr2_then_2 P : height (pyr2_then P) 2 = 2.
Proof. reflexivity. Qed.

Lemma h_pyr2_then_3 P : height (pyr2_then P) 3 = 1.
Proof. reflexivity. Qed.

Lemma h_pyr2_then_4 P m : height (pyr2_then P) (S (S (S (S m)))) = height P m.
Proof.
  unfold height; cbn [stage pyr2_then pyr2_stage FinitePath.height].
  destruct (leb_spec (S (S (S m))) (2 * S (0 + 0))); [lia|].
  replace (S (S (S m)) - S (2 * S (0 + 0))) with m by lia.
  change (FinitePath.height (P m) m) with (height P m); apply height_stage; lia.
Qed.

(** [(ud)^m · P]: [m] hills, then [P]. *)
Fixpoint hills_then (m : nat) (P : Dyckω) : Dyckω :=
  match m with
  | 0 => P
  | S m' => hill_then (hills_then m' P)
  end.

Lemma h_hills_then m P n :
  height (hills_then m P) n = if n <? 2 * m then b2n (odd n) else height P (n - 2 * m).
Proof.
  revert n; induction m as [|m IH]; intros n; cbn [hills_then].
  - destruct (ltb_spec n (2 * 0)); [lia|f_equal; lia].
  - destruct n as [|[|n]].
    + rewrite h_hill_then_0; destruct (ltb_spec 0 (2 * S m)); [reflexivity|lia].
    + rewrite h_hill_then_1; destruct (ltb_spec 1 (2 * S m)); [reflexivity|lia].
    + rewrite h_hill_then_2, IH.
      destruct (ltb_spec n (2 * m)), (ltb_spec (S (S n)) (2 * S m)); try lia.
      * rewrite odd_succ_succ; reflexivity.
      * f_equal; lia.
Qed.
