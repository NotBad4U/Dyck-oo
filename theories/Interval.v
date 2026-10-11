(** * Interface for Intervals and predicates on intervals. *)

From Stdlib Require Import Arith Lia List.

Declare Scope interval_scope.
Delimit Scope interval_scope with interval.
Open Scope interval_scope.

(** [Itv i j] is the interval [[t_i, t_j] = { t | t_i ≤ t ≤ t_j }]. *)
Record interval := Itv { lo : nat; hi : nat }.

(** [isInt n I]: [I := [a, b] ] is an interval of [T_n] such that [1 ≤ a ≤ b ≤ n]. *)
Definition isInt n (I : interval) : Prop := 1 <= lo I /\ lo I <= hi I /\ hi I <= n.

(** [Intω I]: [I] is an interval of [T_ω]. *)
Definition Intω (I : interval) : Prop := 1 <= lo I /\ lo I <= hi I.

(** [J ⊆ I]: [J] is a subinterval of [I]. *)
Definition sub (J I : interval) : Prop :=
  lo I <= lo J /\ lo J <= hi J /\ hi J <= hi I.

Notation "J ⊆ I" := (sub J I) (at level 70, no associativity) : interval_scope.

Lemma sub_trans K J I : K ⊆ J -> J ⊆ I -> K ⊆ I.
Proof. unfold sub; lia. Qed.

Lemma sub_self J I : J ⊆ I -> J ⊆ J.
Proof. unfold sub; lia. Qed.

Lemma isInt_self n I : isInt n I -> I ⊆ I.
Proof. unfold isInt, sub; lia. Qed.

(** A subinterval of an interval of [T_n] is an interval of [T_n]. *)
Lemma isInt_sub n J I : isInt n I -> J ⊆ I -> isInt n J.
Proof. unfold isInt, sub; lia. Qed.

(** The only subinterval of [[t_i, t_i]] is itself. *)
Lemma sub_point J i : J ⊆ Itv i i -> J = Itv i i.
Proof. destruct J as [a b]; unfold sub; cbn; intros H; f_equal; lia. Qed.

Definition bounded (v : interval -> Prop) : Prop :=
  exists N, forall I, Intω I -> v I -> hi I <= N.

Definition unbounded (v : interval -> Prop) : Prop :=
  forall N, exists I, Intω I /\ N <= hi I /\ v I.

Lemma unbounded_not_bounded v : unbounded v -> bounded v -> False.
Proof.
  intros H [N HN]; destruct (H (S N)) as [I [HI [Hh Hv]]]; specialize (HN I HI Hv); lia.
Qed.

(** ** Down-sets of intervals topology aka Alexandrov topology on intervals *)

Definition downset (v : interval -> Prop) : Prop := forall I J, v I -> J ⊆ I -> v J.

Notation "↓ v" := (downset v) (at level 35, right associativity) : interval_scope.

Definition interior (v : interval -> Prop) (I : interval) : Prop := forall J, J ⊆ I -> v J.

Definition closure (v : interval -> Prop) (I : interval) : Prop := exists J, J ⊆ I /\ v J.

Lemma interior_downset v : ↓ interior v.
Proof. intros I J H HJ K HK; exact (H K (sub_trans K J I HK HJ)). Qed.

(** A down-set is its own interior [I ⊆ I]. *)
Lemma interior_downset_id v I : ↓ v -> lo I <= hi I -> (interior v I <-> v I).
Proof.
  intros Hv HI; split.
  - intros H; apply H; unfold sub; lia.
  - intros H J HJ; exact (Hv I J H HJ).
Qed.

Lemma interior_idem v I : interior (interior v) I <-> interior v I.
Proof.
  split.
  - intros H J HJ; exact (H J HJ J (sub_self J I HJ)).
  - intros H J HJ K HK; exact (H K (sub_trans K J I HK HJ)).
Qed.

Lemma closure_idem v I : closure (closure v) I <-> closure v I.
Proof.
  split.
  - intros [J [HJ [K [HK H]]]]; exists K; split; [exact (sub_trans K J I HK HJ)|exact H].
  - intros [J [HJ H]]; exists I; split; [unfold sub in *; lia|exists J; split; assumption].
Qed.

Lemma closure_not_downset : ~ ↓ closure (fun I => I = Itv 1 1).
Proof.
  intros H.
  specialize (H (Itv 1 2) (Itv 2 2)
                ltac:(exists (Itv 1 1); split; [unfold sub; cbn; lia|reflexivity])
                ltac:(unfold sub; cbn; lia)).
  destruct H as [J [HJ E]]; subst J; unfold sub in HJ; cbn in HJ; lia.
Qed.

(* The list of subintervals of [I]. *)
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
