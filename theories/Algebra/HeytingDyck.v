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
    P ⟿ Q = ⋁ { R | P ⊓ R ≤ Q }          ¬ P = P ⟿ ⊥
>>

  [D_n] is finite, so the join is a finite one, taken over the enumeration
  [enumD n]. [P ⟿ Q] is the largest [R] with [P ⊓ R ≤ Q] ([impDP]), which
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

#[export] Instance Dyck_Lattice n : Lattice (Dyck n) :=
  {| lat_Poset := Dyck_Poset n; lat_Meet := Dyck_Meet n; lat_Join := Dyck_Join n |}.

(** [D_n] is a Heyting algebra. *)
#[export] Instance Dyck_HeytingAlgebra n : HeytingAlgebra (Dyck n) :=
  {| ha_Lattice := Dyck_Lattice n; ha_Bot := Dyck_Bot n; ha_Top := Dyck_Top n;
     ha_Distributive := Dyck_Distributive n;
     ha_RelPseudoComplement := Dyck_RelPseudoComplement n |}.

Section ExampleD4.

Import DyckSyntax.

(** ** Example: the Dyck lattice [D₄]

  The figure "The Dyck lattice [D₄], drawn in the geometric order" of the
  paper, every path written as its word. Its Hasse diagram, graded by the
  area under the path:

<<
                     uuuudddd                 ⊤ = u⁴d⁴
                         |
                     uuududdd
                    /        \
            uuduuddd          uuuddudd
           /        \        /        \
   uduuuddd          uudududd          uuudddud
       |      \      /   |   \      /      |
   uduududd          uudduudd          uududdud
       |   \      /      |      \      /   |
       |     \  /        |        \  /     |
       |      /\         |         /\      |
   ududuudd          uduuddud          uuddudud
            \            |            /
                     udududud                 ⊥ = (ud)⁴
>>
*)

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

Lemma card_D4 : length (enumD 4) = 14.
Proof. reflexivity. Qed.

(* [⊥₄ = (ud)⁴] *)
Lemma D4_bot : ⊥ = u d u d u d u d :> Dyck 4.
Proof. reflexivity. Qed.

(* [⊤₄ = u⁴d⁴] *)
Lemma D4_top : ⊤ = u u u u d d d d :> Dyck 4.
Proof. apply eqD_spec; vm_compute; reflexivity. Qed.

Lemma D4_hneg : ¬ (u u d d u d u d) = u d u u u d d d :> Dyck 4.
Proof. apply eqD_spec; vm_compute; reflexivity. Qed.

Lemma D4_not_boolean : (u u d d u d u d) ⊔ ¬ (u u d d u d u d) <> ⊤ :> Dyck 4.
Proof.
  rewrite D4_hneg; intros E; apply eqD_spec in E.
  vm_compute in E; discriminate E.
Qed.

End ExampleD4.
