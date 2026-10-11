(** * Lattice interface and theory based on Setoid relation *)
From Stdlib Require Import RelationClasses Morphisms Setoid.

Class Poset (X : Type) := {
  po_le : relation X;
  po_eq : relation X;
  po_le_PreOrder :: PreOrder po_le;
  po_eqE : forall x y, po_eq x y <-> po_le x y /\ po_le y x
}.

Declare Scope lattice_scope.
Delimit Scope lattice_scope with lattice.
Open Scope lattice_scope.

Notation "x ≤ y" := (po_le x y) (at level 70, no associativity) : lattice_scope.
Notation "x ≡ y" := (po_eq x y) (at level 70, no associativity) : lattice_scope.

Class Join X {P : Poset X} := {
  join : X -> X -> X;
  leUx : forall x y z, join x y ≤ z <-> x ≤ z /\ y ≤ z
}.

Class Meet X {P : Poset X} := {
  meet : X -> X -> X;
  lexI : forall x y z, z ≤ meet x y <-> z ≤ x /\ z ≤ y
}.

Class Bot X {P : Poset X} := { bot : X; le0x : forall x, bot ≤ x }.

Class Top X {P : Poset X} := { top : X; lex1 : forall x, x ≤ top }.

Notation "x ⊔ y" := (join x y) (at level 50, left associativity) : lattice_scope.
Notation "x ⊓ y" := (meet x y) (at level 40, left associativity) : lattice_scope.
Notation "⊥" := bot : lattice_scope.
Notation "⊤" := top : lattice_scope.

Class Distributive X {P : Poset X} {M : Meet X} {J : Join X} :=
  meetUr : forall x y z, x ⊓ (y ⊔ z) ≡ x ⊓ y ⊔ x ⊓ z.

Class RelPseudoComplement X {P : Poset X} {M : Meet X} := {
  himp : X -> X -> X;
  himpP : forall x y z, x ⊓ z ≤ y <-> z ≤ himp x y
}.

Notation "x ⟿ y" := (himp x y) (at level 60, right associativity) : lattice_scope.

Class PseudoComplement X {P : Poset X} {M : Meet X} {B : Bot X} := {
  pneg : X -> X;
  pnegP : forall x z, x ⊓ z ≤ ⊥ <-> z ≤ pneg x
}.

Notation "¬ x" := (pneg x) (at level 35, right associativity) : lattice_scope.

#[export] Instance RelPseudoComplement_PseudoComplement {X : Type} {P : Poset X}
  {M : Meet X} {R : RelPseudoComplement X} {B : Bot X} : PseudoComplement X :=
  {| pneg x := x ⟿ ⊥; pnegP x z := himpP x ⊥ z |}.

Class JoinSemilattice X {P : Poset X} := { jsl_Join :: Join X }.

Class MeetSemilattice X {P : Poset X} := { msl_Meet :: Meet X }.

Class Lattice X {P : Poset X} := {
  lat_JoinSemilattice :: JoinSemilattice X;
  lat_MeetSemilattice :: MeetSemilattice X
}.

Class HeytingAlgebra X {P : Poset X} := {
  ha_Lattice :: Lattice X;
  ha_Bot :: Bot X;
  ha_Top :: Top X;
  ha_Distributive :: Distributive X;
  ha_RelPseudoComplement :: RelPseudoComplement X
}.

Section PosetTheory.

Context {X : Type} {P : Poset X}.

Lemma lexx (x : X) : x ≤ x.
Proof. reflexivity. Qed.

Lemma le_trans {x y z : X} : x ≤ y -> y ≤ z -> x ≤ z.
Proof. intros xy yz; transitivity y; assumption. Qed.

Lemma le_anti {x y : X} : x ≤ y -> y ≤ x -> x ≡ y.
Proof. intros xy yx; apply po_eqE; split; assumption. Qed.

(** [is_sup S s]: [s] is the join [⋁ S] of the set [S], its least upper
  bound. It is unique up to [≡]. *)
Definition is_sup (S : X -> Prop) (s : X) : Prop :=
  (forall x, S x -> x ≤ s) /\ (forall u, (forall x, S x -> x ≤ u) -> s ≤ u).

Lemma is_sup_unique S s t : is_sup S s -> is_sup S t -> s ≡ t.
Proof. intros [Us Ls] [Ut Lt]; apply le_anti; [apply Ls, Ut|apply Lt, Us]. Qed.

(** A greatest element of a set is its join. *)
Lemma greatest_is_sup (S : X -> Prop) s : S s -> (forall x, S x -> x ≤ s) -> is_sup S s.
Proof. intros Hs Hub; split; [exact Hub|intros u Hu; exact (Hu s Hs)]. Qed.

End PosetTheory.

#[export] Instance po_eq_Equivalence {X : Type} {P : Poset X} :
  Equivalence (@po_eq X P).
Proof.
  split.
  - intros x; apply le_anti; apply lexx.
  - intros x y [xy yx]%po_eqE; apply le_anti; assumption.
  - intros x y z [xy yx]%po_eqE [yz zy]%po_eqE.
    apply le_anti; eapply le_trans; eassumption.
Qed.

#[export] Instance po_le_Proper {X : Type} {P : Poset X} :
  Proper (po_eq ==> po_eq ==> iff) (@po_le X P).
Proof.
  intros x x' [xx' x'x]%po_eqE y y' [yy' y'y]%po_eqE; split; intros H.
  - exact (le_trans x'x (le_trans H yy')).
  - exact (le_trans xx' (le_trans H y'y)).
Qed.

Section LatticeTheory.

Context {X : Type} {P : Poset X}.

Section JoinTheory.

Context {J : Join X}.

Lemma leUl (x y : X) : x ≤ x ⊔ y.
Proof. exact (proj1 (proj1 (leUx x y (x ⊔ y)) (lexx _))). Qed.

Lemma leUr (x y : X) : y ≤ x ⊔ y.
Proof. exact (proj2 (proj1 (leUx x y (x ⊔ y)) (lexx _))). Qed.

Lemma leU2 {x y x' y' : X} : x ≤ x' -> y ≤ y' -> x ⊔ y ≤ x' ⊔ y'.
Proof.
  intros xx' yy'; apply leUx; split.
  - exact (le_trans xx' (leUl _ _)).
  - exact (le_trans yy' (leUr _ _)).
Qed.

End JoinTheory.

Section MeetTheory.

Context {M : Meet X}.

Lemma leIl (x y : X) : x ⊓ y ≤ x.
Proof. exact (proj1 (proj1 (lexI x y (x ⊓ y)) (lexx _))). Qed.

Lemma leIr (x y : X) : x ⊓ y ≤ y.
Proof. exact (proj2 (proj1 (lexI x y (x ⊓ y)) (lexx _))). Qed.

Lemma leI2 {x y x' y' : X} : x ≤ x' -> y ≤ y' -> x ⊓ y ≤ x' ⊓ y'.
Proof.
  intros xx' yy'; apply lexI; split.
  - exact (le_trans (leIl _ _) xx').
  - exact (le_trans (leIr _ _) yy').
Qed.

Lemma meetC_le (x y : X) : x ⊓ y ≤ y ⊓ x.
Proof. apply lexI; split; [apply leIr|apply leIl]. Qed.

Context {B : Bot X} {T : Top X}.

Lemma lex0 (x : X) : x ≤ ⊥ <-> x ≡ ⊥.
Proof.
  split.
  - intros x0; exact (le_anti x0 (le0x x)).
  - intros [x0 _]%po_eqE; exact x0.
Qed.

Lemma meet0x (x : X) : ⊥ ⊓ x ≡ ⊥.
Proof. apply lex0, leIl. Qed.

Lemma meet1x (x : X) : ⊤ ⊓ x ≡ x.
Proof.
  apply le_anti; [apply leIr|].
  apply lexI; split; [apply lex1|apply lexx].
Qed.

End MeetTheory.

End LatticeTheory.

#[export] Instance join_Proper {X : Type} {P : Poset X} {J : Join X} :
  Proper (po_eq ==> po_eq ==> po_eq) (@join X P J).
Proof.
  intros x x' [? ?]%po_eqE y y' [? ?]%po_eqE.
  apply le_anti; apply leU2; assumption.
Qed.

#[export] Instance meet_Proper {X : Type} {P : Poset X} {M : Meet X} :
  Proper (po_eq ==> po_eq ==> po_eq) (@meet X P M).
Proof.
  intros x x' [? ?]%po_eqE y y' [? ?]%po_eqE.
  apply le_anti; apply leI2; assumption.
Qed.

Section DistributiveTheory.

Context {X : Type} {P : Poset X} {M : Meet X} {J : Join X}.

(** The half of [meetUr] that holds in every lattice. *)
Lemma meetU_ge (x y z : X) : x ⊓ y ⊔ x ⊓ z ≤ x ⊓ (y ⊔ z).
Proof.
  apply leUx; split; apply leI2.
  - apply lexx.
  - apply leUl.
  - apply lexx.
  - apply leUr.
Qed.

Context {D : Distributive X}.

Lemma meetUr_le (x y z : X) : x ⊓ (y ⊔ z) ≤ x ⊓ y ⊔ x ⊓ z.
Proof. exact (proj1 (proj1 (po_eqE _ _) (meetUr x y z))). Qed.

Lemma joinIr (x y z : X) : x ⊔ (y ⊓ z) ≡ (x ⊔ y) ⊓ (x ⊔ z).
Proof.
  apply le_anti.
  - apply lexI; split; apply leU2.
    + apply lexx.
    + apply leIl.
    + apply lexx.
    + apply leIr.
  - apply (le_trans (meetUr_le _ _ _)), leUx; split.
    + exact (le_trans (leIr _ _) (leUl _ _)).
    + apply (le_trans (meetC_le _ _)), (le_trans (meetUr_le _ _ _)), leUx; split.
      * exact (le_trans (leIr _ _) (leUl _ _)).
      * exact (le_trans (meetC_le _ _) (leUr _ _)).
Qed.

End DistributiveTheory.

Section RelPseudoComplementTheory.

Context {X : Type} {P : Poset X} {M : Meet X} {R : RelPseudoComplement X}.

Lemma meet_himp (x y : X) : x ⊓ (x ⟿ y) ≤ y.
Proof. apply himpP, lexx. Qed.

Lemma himp_is_sup (x y : X) : is_sup (fun z => x ⊓ z ≤ y) (x ⟿ y).
Proof. apply greatest_is_sup; [apply meet_himp|intros z Hz; apply himpP, Hz]. Qed.

End RelPseudoComplementTheory.

Section PseudoComplementTheory.

Context {X : Type} {P : Poset X} {M : Meet X} {B : Bot X} {T : Top X}.
Context {C : PseudoComplement X}.

Lemma pnegE (x z : X) : z ≤ ¬ x <-> x ⊓ z ≡ ⊥.
Proof. rewrite <- pnegP; apply lex0. Qed.

Lemma meet_pneg (x : X) : x ⊓ ¬ x ≡ ⊥.
Proof. apply pnegE, lexx. Qed.

Lemma pneg0 : ¬ ⊥ ≡ (⊤ : X).
Proof. apply le_anti; [apply lex1|apply pnegE, meet0x]. Qed.

Lemma pneg1 : ¬ ⊤ ≡ (⊥ : X).
Proof.
  apply lex0, (@le_trans _ _ _ (⊤ ⊓ ¬ ⊤)).
  - apply lexI; split; [apply lex1|apply lexx].
  - apply lex0, meet_pneg.
Qed.

End PseudoComplementTheory.
