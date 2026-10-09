(** * The Dyck lattice [D_n] as a Heyting algebra *)

From Stdlib Require Import Arith Bool Lia List Permutation RelationClasses.
Import Nat.
From Dyck Require Import Lattice Dyck Words.
Import ListNotations FinitePath.
Open Scope lattice_scope.

Definition leD {n} (P Q : Dyck n) : Prop := forall i, height P i <= height Q i.

Definition leDb {n} (P Q : Dyck n) : bool :=
  forallb (fun i => height P i <=? height Q i) (seq 0 (S (2 * n))).

Lemma leDb_spec {n} (P Q : Dyck n) : leDb P Q = true <-> leD P Q.
Proof.
  unfold leDb, leD; rewrite forallb_forall; split.
  - intros H i; destruct (le_gt_cases i (2 * n)) as [lei|lti].
    + apply leb_le, H, in_seq; lia.
    + rewrite !height_ge by lia; lia.
  - intros H i _; apply leb_le, H.
Qed.

(** A path is determined by its heights. *)
Lemma leD_eqE {n} (P Q : Dyck n) : P = Q <-> leD P Q /\ leD Q P.
Proof.
  split.
  - intros <-; split; intros i; lia.
  - intros [PQ QP]; apply h_inj; intros i.
    specialize (PQ i); specialize (QP i); lia.
Qed.

Lemma leD_meetD {n} (P Q R : Dyck n) : leD R (meetD P Q) <-> leD R P /\ leD R Q.
Proof.
  unfold leD; split.
  - intros H; split; intros i; specialize (H i); rewrite h_meetD in H; lia.
  - intros [HP HQ] i; rewrite h_meetD; specialize (HP i); specialize (HQ i); lia.
Qed.

Lemma leD_joinD {n} (P Q R : Dyck n) : leD (joinD P Q) R <-> leD P R /\ leD Q R.
Proof.
  unfold leD; split.
  - intros H; split; intros i; specialize (H i); rewrite h_joinD in H; lia.
  - intros [HP HQ] i; rewrite h_joinD; specialize (HP i); specialize (HQ i); lia.
Qed.

Lemma meetD_joinD {n} (P Q R : Dyck n) :
  leD (meetD P (joinD Q R)) (joinD (meetD P Q) (meetD P R)).
Proof. intros i; rewrite !h_meetD, !h_joinD, !h_meetD; lia. Qed.

(** [⊥ = (ud)ⁿ] lies below every path, since the height after an odd number
  of steps is odd, hence at least [1]; [⊤ = uⁿdⁿ] lies above every path,
  since a path climbs at most one level per step. *)

Lemma le0D {n} (P : Dyck n) : leD (hills n) P.
Proof.
  intros i; destruct (le_gt_cases i (2 * n)) as [le|gt].
  - rewrite height_hills by exact le.
    destruct (odd i) eqn:oi; simpl; [|lia].
    pose proof (odd_height P i le) as Hodd; rewrite oi in Hodd.
    revert Hodd; destruct (height P i); intros Hodd; [discriminate Hodd|lia].
  - rewrite height_ge by lia; lia.
Qed.

Lemma leD1 {n} (P : Dyck n) : leD P (pyramid n).
Proof.
  intros i; rewrite height_pyramid.
  pose proof (height_lei P i); pose proof (height_le_sub P i); lia.
Qed.

#[export] Instance leD_PreOrder n : PreOrder (@leD n).
Proof.
  split.
  - intros P i; lia.
  - intros P Q R PQ QR i; specialize (PQ i); specialize (QR i); lia.
Qed.

#[export] Instance Dyck_Poset n : Poset (Dyck n) :=
  {| po_le := @leD n; po_eq := Logic.eq;
     po_le_PreOrder := leD_PreOrder n; po_eqE := @leD_eqE n |}.

#[export] Instance Dyck_Meet n : Meet (Dyck n) :=
  {| meet := @meetD n; lexI := @leD_meetD n |}.

#[export] Instance Dyck_Join n : Join (Dyck n) :=
  {| join := @joinD n; leUx := @leD_joinD n |}.

#[export] Instance Dyck_Distributive n : Distributive (Dyck n).
Proof. intros P Q R; apply le_anti; [apply meetD_joinD|apply meetU_ge]. Qed.

#[export] Instance Dyck_Bot n : Bot (Dyck n) :=
  {| bot := hills n; le0x := @le0D n |}.

#[export] Instance Dyck_Top n : Top (Dyck n) :=
  {| top := pyramid n; lex1 := @leD1 n |}.

(** ** Pseudo-complements

  As in the section "Completion" of the paper, the implication is the
  relative pseudo-complement and the negation is the pseudo-complement:

<<
    P ↛ Q = ⋁ { R | P ⊓ R ≤ Q }          ¬ P = P ↛ ⊥
>>

  [D_n] is finite, so the join is a finite one, taken over the enumeration
  [enumD n]. [P ↛ Q] is the largest [R] with [P ⊓ R ≤ Q] ([impDP]), which
  makes [D_n] a Heyting algebra. *)

Definition impD {n} (P Q : Dyck n) : Dyck n :=
  fold_right join ⊥ (filter (fun R => leDb (P ⊓ R) Q) (enumD n)).

Lemma le_foldr_join {n} (s : list (Dyck n)) R : In R s -> R ≤ fold_right join ⊥ s.
Proof.
  induction s as [|Q s IH]; [intros []|intros [<-|RS]].
  - apply leUl.
  - exact (le_trans (IH RS) (leUr _ _)).
Qed.

Lemma meet_impD {n} (P Q : Dyck n) : P ⊓ impD P Q ≤ Q.
Proof.
  unfold impD; induction (enumD n) as [|R s IH]; cbn [filter].
  - exact (le_trans (leIr _ _) (le0x _)).
  - destruct (leDb (P ⊓ R) Q) eqn:PRQ; [|exact IH].
    apply leDb_spec in PRQ.
    apply (le_trans (meetUr_le _ _ _)), leUx; split; [exact PRQ|exact IH].
Qed.

Lemma impDP {n} (P Q R : Dyck n) : P ⊓ R ≤ Q <-> R ≤ impD P Q.
Proof.
  split; intros H.
  - apply le_foldr_join, filter_In; split; [apply mem_enumD|].
    apply leDb_spec; exact H.
  - exact (le_trans (leI2 (lexx P) H) (meet_impD P Q)).
Qed.

#[export] Instance Dyck_RelPseudoComplement n : RelPseudoComplement (Dyck n) :=
  {| himp := @impD n; himpP := @impDP n |}.

Lemma himpE {n} (P Q : Dyck n) : P ↛ Q = impD P Q.
Proof. reflexivity. Qed.

(** ** Example: the Dyck lattice [D₄]

  The figure "The Dyck lattice [D₄], drawn in the geometric order" of the
  paper, every path written as its word. *)

Definition ltDb {n} (P Q : Dyck n) : bool := negb (eqD Q P) && leDb P Q.

(** [Q] covers [P]: [P < Q] with nothing strictly in between. Quantifying
  over the explicit enumeration [enumD n] keeps it computable. *)
Definition covers {n} (P Q : Dyck n) : bool :=
  ltDb P Q && forallb (fun R => negb (ltDb P R && ltDb R Q)) (enumD n).

Lemma covers_spec {n} (P Q : Dyck n) :
  covers P Q = true <->
  ltDb P Q = true /\ forall R, ltDb P R && ltDb R Q = false.
Proof.
  unfold covers; rewrite andb_true_iff, forallb_forall.
  split; intros [PQ H]; split; try exact PQ.
  - intros R; apply negb_true_iff, H, mem_enumD.
  - intros R _; apply negb_true_iff, H.
Qed.

(** A list of paths contains another one when it contains each of its paths,
  which is decided by comparing words. *)
Lemma inclD {n} (s1 s2 : list (Dyck n)) :
  forallb (fun P => existsb (eqD P) s2) s1 = true -> incl s1 s2.
Proof.
  rewrite forallb_forall; intros H P HP.
  apply H, existsb_exists in HP as [Q [inQ EQ]].
  apply eqD_spec in EQ; subst Q; exact inQ.
Qed.

(* Section D4.

Import DyckSyntax.

(** The fourteen paths of [D₄], from bottom to top as in the figure. *)
Definition D4 : list (Dyck 4) :=
  [u d u d u d u d;
   u d u d u u d d;
   u d u u d d u d;
   u u d d u d u d;
   u d u u d u d d;
   u u d d u u d d;
   u u d u d d u d;
   u d u u u d d d;
   u u d u d u d d;
   u u u d d d u d;
   u u d u u d d d;
   u u u d d u d d;
   u u u d u d d d;
   u u u u d d d d].


(** They are all of [D₄], each exactly once. *)
Lemma D4_enum : Permutation D4 (enumD 4).
Proof.
  assert (incl1 : incl (enumD 4) D4) by (apply inclD; vm_compute; reflexivity).
  apply NoDup_Permutation.
  - apply (NoDup_incl_NoDup (NoDup_enumD 4)); [|exact incl1].
    apply leb_le; vm_compute; reflexivity.
  - apply NoDup_enumD.
  - intros P; split; intros _; [apply mem_enumD|apply incl1, mem_enumD].
Qed.

(** [enumD 4] has no repetition, so this is the cardinal of [D₄]. *)
Lemma card_D4 : length (enumD 4) = 14.
Proof. vm_compute; reflexivity. Qed.

(** [⊥₄ = (ud)⁴] and [⊤₄ = u⁴d⁴]. *)
Lemma D4_bot : ⊥ = u d u d u d u d :> Dyck 4.
Proof. reflexivity. Qed.

Lemma D4_top : ⊤ = u u u u d d d d :> Dyck 4.
Proof. apply eqD_spec; vm_compute; reflexivity. Qed.

(** The edges of the figure, each from the lower to the upper path. *)
Definition D4_edges : list (Dyck 4 * Dyck 4) :=
  [(u d u d u d u d, u u d d u d u d);
   (u d u d u d u d, u d u u d d u d);
   (u d u d u d u d, u d u d u u d d);
   (u d u d u u d d, u u d d u u d d);
   (u d u d u u d d, u d u u d u d d);
   (u d u u d d u d, u u d u d d u d);
   (u d u u d d u d, u d u u d u d d);
   (u u d d u d u d, u u d u d d u d);
   (u u d d u d u d, u u d d u u d d);
   (u d u u d u d d, u u d u d u d d);
   (u d u u d u d d, u d u u u d d d);
   (u u d d u u d d, u u d u d u d d);
   (u u d u d d u d, u u u d d d u d);
   (u u d u d d u d, u u d u d u d d);
   (u d u u u d d d, u u d u u d d d);
   (u u d u d u d d, u u u d d u d d);
   (u u d u d u d d, u u d u u d d d);
   (u u u d d d u d, u u u d d u d d);
   (u u d u u d d d, u u u d u d d d);
   (u u u d d u d d, u u u d u d d d);
   (u u u d u d d d, u u u u d d d d)].


(** The Hasse diagram of the figure is exactly the covering relation of [D₄]. *)
(* Lemma D4_hasse : forall P Q : Dyck 4, covers P Q = true <-> In (P, Q) D4_edges. *)

(** [D₄] is a Heyting algebra but not a Boolean one: the pseudo-complement
  of [u u d d u d u d] (the interval [[1,1]] in the paper's table) is
  [u d u u u d d d] (the interval [[2,3]]), and their join is not [⊤]. *)
Lemma D4_hneg : ¬ (u u d d u d u d) = u d u u u d d d :> Dyck 4.
Proof. apply eqD_spec; vm_compute; reflexivity. Qed.

Lemma D4_not_boolean : (u u d d u d u d) ⊔ ¬ (u u d d u d u d) <> ⊤ :> Dyck 4.
Proof.
  rewrite D4_hneg; intros E; apply eqD_spec in E.
  vm_compute in E; discriminate E.
Qed.

End D4. *)
