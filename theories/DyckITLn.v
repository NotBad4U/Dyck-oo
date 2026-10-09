(** * Theorem 3.1: [D_n ≅ [Θ_(n-1)]] *)

From Stdlib Require Import Arith Bool Lia List.
Import Nat.
From Dyck Require Import Lattice Dyck Words HeytingDyck ITLn.
Import EqNotations FinitePath.

Open Scope lattice_scope.
Open Scope itl_scope.

(** ** Heights *)

Lemma b2n_le_1 b : b2n b <= 1.
Proof. destruct b; cbn; lia. Qed.

(** [height_hills] for every [i], past the end of the path too ([height_ge]): the
  form in which the floor [⊥] enters the heights computed below. *)
Lemma h_hills_b2n n i : height (hills n) i = b2n (odd i && (i <? 2 * n)).
Proof.
  destruct (ltb_spec i (2 * n)) as [lt|ge].
  - rewrite height_hills by lia; destruct (odd i); reflexivity.
  - rewrite height_ge by exact ge; rewrite andb_false_r; reflexivity.
Qed.

Lemma odd_double k : odd (2 * k) = false.
Proof. rewrite <- (add_0_l (2 * k)), odd_add_mul_2; reflexivity. Qed.

(** A path moves by one level at each step. *)
Lemma h_step {n} (P : Dyck n) x : height P (S x) <= S (height P x) /\ height P x <= S (height P (S x)).
Proof.
  destruct (le_gt_cases (2 * n) x) as [ge|lt].
  - rewrite !height_ge by lia; lia.
  - rewrite !h_up; pose proof (up_step (word P) x).
    pose proof (up_double P x ltac:(lia)); pose proof (up_double P (S x) ltac:(lia)).
    lia.
Qed.

Definition dist (x y : nat) : nat := (x - y) + (y - x).

Lemma h_lip {n} (P : Dyck n) x d : height P x <= height P (x + d) + d /\ height P (x + d) <= height P x + d.
Proof.
  induction d as [|d IH]; [rewrite !add_0_r; lia|].
  replace (x + S d) with (S (x + d)) by lia; pose proof (h_step P (x + d)); lia.
Qed.

(** Heights at two abscissas differ by at most their distance. *)
Lemma h_dist {n} (P : Dyck n) x y : height P y <= height P x + dist x y.
Proof.
  unfold dist; destruct (le_ge_cases x y) as [le|le].
  - pose proof (h_lip P x (y - x)) as H; replace (x + (y - x)) with y in H by lia; lia.
  - pose proof (h_lip P y (x - y)) as H; replace (y + (x - y)) with x in H by lia; lia.
Qed.

(** ** The paths [J_I] *)

(** [pre_hills j X] is the path [(ud)^j X]. *)
Fixpoint pre_hills (j : nat) {k} (X : Dyck k) : Dyck (j + k) :=
  match j return Dyck (j + k) with
  | 0 => X
  | S j' => ud eps (pre_hills j' X)
  end.

Lemma h_pre_hills j {k} (X : Dyck k) x :
  height (pre_hills j X) x = if x <? 2 * j then b2n (odd x) else height X (x - 2 * j).
Proof.
  revert x; induction j as [|j IH]; intros x.
  - cbn [pre_hills]; rewrite mul_0_r, sub_0_r; reflexivity.
  - destruct x as [|[|x]].
    + rewrite h0; reflexivity.
    + replace (1 <? 2 * S j) with true by (symmetry; apply ltb_lt; lia).
      reflexivity.
    + change (height (pre_hills (S j) X) (S (S x))) with (height (pre_hills j X) (x - 0)).
      rewrite sub_0_r, IH.
      replace (S (S x) <? 2 * S j) with (x <? 2 * j)
        by (apply eq_iff_eq_true; rewrite !ltb_lt; lia).
      replace (S (S x) - 2 * S j) with (x - 2 * j) by lia.
      rewrite odd_succ, even_succ; reflexivity.
Qed.

(** [ud (pyramid p) (hills r)] is the path [u^(p+1) d^(p+1) (ud)^r]. *)
Lemma h_core p r y :
  height (ud (pyramid p) (hills r)) y =
  if y <=? 2 * S p then min y (2 * S p - y)
  else b2n (odd y && (y <? 2 * S p + 2 * r)).
Proof.
  destruct y as [|j]; [reflexivity|].
  rewrite hS, height_pyramid, h_hills_b2n.
  destruct (leb_spec j (2 * p)) as [hj|hj];
    destruct (leb_spec (S j) (2 * S p)) as [hj'|hj']; try lia.
  - replace (j - S (2 * p)) with 0 by lia.
    change (b2n (odd 0 && (0 <? 2 * r))) with 0; lia.
  - f_equal; f_equal.
    + replace (S j) with ((j - S (2 * p)) + 2 * S p) by lia.
      rewrite odd_add_mul_2; reflexivity.
    + apply eq_iff_eq_true; rewrite !ltb_lt; lia.
Qed.

Section J.

Variable m : nat.

(** For [I = [a, b]], the pyramid of [J_I] has height [peak_h I = b - a + 2]
  and its top at the abscissa [peak_x I = a + b]. *)
Definition peak_h (I : interval) : nat := hi I - lo I + 2.
Definition peak_x (I : interval) : nat := lo I + hi I.

(** [J I] is [J_I = (ud)^(a-1) u^k d^k (ud)^(m-b)], with [k = b - a + 2], a
  path of [D_(m+1)] when [I] is an interval of [T_m]. *)
Definition J (I : interval) : Dyck (S m) :=
  match eq_dec ((lo I - 1) + S ((hi I - lo I + 1) + (m - hi I))) (S m) with
  | left e =>
      rew [Dyck] e in pre_hills (lo I - 1) (ud (pyramid (hi I - lo I + 1)) (hills (m - hi I)))
  | right _ => hills (S m)
  end.

(** [J_I] is the floor [⊥] raised by the pyramid. *)
Lemma h_J I x : Int m I ->
  height (J I) x = max (b2n (odd x && (x <? 2 * S m))) (peak_h I - dist x (peak_x I)).
Proof.
  destruct I as [a b]; unfold Int, J, peak_h, peak_x, dist; cbn [lo hi]; intros HI.
  match goal with |- context [eq_dec ?u ?v] => destruct (eq_dec u v) as [e|ne] end;
    [|exfalso; lia].
  rewrite h_cast, h_pre_hills.
  destruct (ltb_spec x (2 * (a - 1))) as [hx|hx].
  - replace (x <? 2 * S m) with true by (symmetry; apply ltb_lt; lia).
    rewrite andb_true_r; lia.
  - rewrite h_core.
    destruct (leb_spec (x - 2 * (a - 1)) (2 * S (b - a + 1))) as [hy|hy].
    + pose proof (b2n_le_1 (odd x && (x <? 2 * S m))) as Hb.
      destruct (eq_dec x (2 * (a - 1))) as [E|ne1].
      * assert (Ho : odd x = false) by (rewrite E; apply odd_double).
        rewrite Ho; cbn [andb b2n]; lia.
      * destruct (eq_dec x (2 * (a - 1 + S (b - a + 1)))) as [E|ne2].
        -- assert (Ho : odd x = false) by (rewrite E; apply odd_double).
           rewrite Ho; cbn [andb b2n]; lia.
        -- lia.
    + assert (Ho : odd (x - 2 * (a - 1)) = odd x).
      { rewrite <- (odd_add_mul_2 (x - 2 * (a - 1)) (a - 1)); f_equal; lia. }
      rewrite Ho.
      replace (x - 2 * (a - 1) <? 2 * S (b - a + 1) + 2 * (m - b)) with (x <? 2 * S m)
        by (apply eq_iff_eq_true; rewrite !ltb_lt; lia).
      lia.
Qed.

(** [J_I ≤ P] exactly when [P] reaches the top of the pyramid of [J_I]. *)
Lemma J_le_iff I (P : Dyck (S m)) : Int m I -> (leD (J I) P <-> peak_h I <= height P (peak_x I)).
Proof.
  intros HI; split.
  - intros H; specialize (H (peak_x I)); rewrite h_J in H by exact HI.
    unfold dist in H; lia.
  - intros H x; rewrite h_J by exact HI.
    pose proof (le0D P x) as H0; rewrite h_hills_b2n in H0.
    pose proof (h_dist P x (peak_x I)).
    apply max_lub; [exact H0|lia].
Qed.

(** The lemma of the definition "interval representation":
  [J_I ≤ J_I' ⟺ I ⊆ I']. *)
Lemma J_mono I K : Int m I -> Int m K -> (leD (J I) (J K) <-> I ⊆ K).
Proof.
  intros HI HK; rewrite J_le_iff, h_J by assumption.
  pose proof (b2n_le_1 (odd (peak_x I) && (peak_x I <? 2 * S m))).
  destruct I as [a b], K as [c d]; unfold Int, sub, peak_h, peak_x, dist in *; cbn in *.
  lia.
Qed.

Lemma h_fold n (l : list (Dyck n)) x :
  height (fold_right joinD (hills n) l) x =
  fold_right max (height (hills n) x) (map (fun P => height P x) l).
Proof.
  induction l as [|P l IH]; cbn [fold_right map]; [reflexivity|].
  rewrite h_joinD, IH; reflexivity.
Qed.

Lemma le_fold_max k b l :
  k <= fold_right max b l <-> k <= b \/ exists y, In y l /\ k <= y.
Proof.
  induction l as [|y l IH]; cbn [fold_right In].
  - split; [now left|intros [H|[y [[] _]]]; exact H].
  - rewrite max_le_iff, IH; split.
    + intros [H|[H|[z [Hz H]]]].
      * right; exists y; split; [left; reflexivity|exact H].
      * left; exact H.
      * right; exists z; split; [right; exact Hz|exact H].
    + intros [H|[z [[<-|Hz] H]]].
      * right; left; exact H.
      * left; exact H.
      * right; right; exists z; split; [exact Hz|exact H].
Qed.

(** [J_K] is below a join of [J_I]'s exactly when [K] is below one of the
  [I]'s. *)
Lemma J_le_join K (l : list interval) : Int m K -> (forall I, In I l -> Int m I) ->
  (leD (J K) (fold_right joinD (hills (S m)) (map J l)) <-> exists I, In I l /\ K ⊆ I).
Proof.
  intros HK Hl; rewrite J_le_iff, h_fold, le_fold_max, map_map by exact HK; split.
  - intros [H|[y [Hy H]]].
    + exfalso; rewrite h_hills_b2n in H; unfold peak_h in H.
      pose proof (b2n_le_1 (odd (peak_x K) && (peak_x K <? 2 * S m))); lia.
    + apply in_map_iff in Hy as [I [<- HI]]; exists I; split; [exact HI|].
      apply (proj1 (J_mono K I HK (Hl I HI))), (proj2 (J_le_iff K (J I) HK)), H.
  - intros [I [HI HKI]]; right; exists (height (J I) (peak_x K)); split.
    + apply in_map_iff; exists I; split; [reflexivity|exact HI].
    + apply (proj1 (J_le_iff K (J I) HK)), (proj2 (J_mono K I HK (Hl I HI))), HKI.
Qed.

(** [J_K] is join-prime. *)
Lemma J_le_joinD K (P Q : Dyck (S m)) : Int m K ->
  (leD (J K) (joinD P Q) <-> leD (J K) P \/ leD (J K) Q).
Proof. intros HK; rewrite !(J_le_iff K _ HK), h_joinD; lia. Qed.

(** A path is determined by the [J_I] below it: if every [J_I] below [P] is
  below [Q], then [P ≤ Q]. *)
Lemma J_embed (P Q : Dyck (S m)) :
  (forall I, Int m I -> leD (J I) P -> leD (J I) Q) -> leD P Q.
Proof.
  intros H x.
  destruct (le_gt_cases (height P x) 1) as [le1|gt1].
  - (* at height [0] or [1], [P] is on the floor [⊥], which [Q] is above *)
    destruct (height P x) as [|[|y]] eqn:E; [lia| |lia].
    assert (Hx : x < 2 * S m).
    { destruct (le_gt_cases (2 * S m) x) as [ge|lt]; [|exact lt].
      rewrite height_ge in E by exact ge; discriminate E. }
    pose proof (odd_height P x ltac:(lia)) as Ho; rewrite E in Ho.
    pose proof (le0D Q x) as HQ; rewrite h_hills_b2n, <- Ho in HQ.
    replace (x <? 2 * S m) with true in HQ by (symmetry; apply ltb_lt; exact Hx).
    exact HQ.
  - (* at height [y ≥ 2], [P] reaches the top of [J_I] for [I = [d + 1, d + y - 1]] *)
    assert (Hx : x < 2 * S m).
    { destruct (le_gt_cases (2 * S m) x) as [ge|lt]; [|exact lt].
      rewrite height_ge in gt1 by exact ge; lia. }
    pose proof (height_lei P x) as Hlei; pose proof (height_le_sub P x) as Hsub.
    pose proof (odd_height P x ltac:(lia)) as Ho.
    assert (He : Even (x - height P x)).
    { apply even_spec; rewrite even_sub by exact Hlei.
      rewrite <- !negb_odd, Ho; apply eqb_reflx. }
    destruct He as [d Hd].
    set (I := Itv (S d) (d + height P x - 1)).
    assert (HI : Int m I) by (unfold Int, I; cbn; lia).
    assert (Hc : peak_x I = x) by (unfold peak_x, I; cbn; lia).
    assert (Hk : peak_h I = height P x) by (unfold peak_h, I; cbn; lia).
    assert (HP : leD (J I) P) by (apply (J_le_iff I P HI); rewrite Hc, Hk; lia).
    pose proof (proj1 (J_le_iff I Q HI) (H I HI HP)) as HQ.
    rewrite Hc, Hk in HQ; exact HQ.
Qed.

(** [J_K ≤ P ↛ Q] exactly when every [J_L ≤ J_K] below [P] is below [Q]. *)
Lemma J_le_impD K (P Q : Dyck (S m)) : Int m K ->
  (leD (J K) (impD P Q) <-> forall L, Int m L -> L ⊆ K -> leD (J L) P -> leD (J L) Q).
Proof.
  intros HK; split.
  - intros H L HL HLK HLP.
    pose proof (proj2 (J_mono L K HL HK) HLK) as HJ.
    assert (H1 : leD (J L) (impD P Q)) by (intros x; specialize (HJ x); specialize (H x); lia).
    assert (H2 : leD (meetD P (J L)) Q) by exact (proj2 (impDP P Q (J L)) H1).
    intros x; specialize (H2 x); specialize (HLP x); rewrite h_meetD in H2; lia.
  - intros H.
    apply (proj1 (impDP P Q (J K))); change (leD (meetD P (J K)) Q).
    apply J_embed; intros I HI HIPK.
    apply leD_meetD in HIPK as [HIP HIK].
    exact (H I HI (proj1 (J_mono I K HI HK) HIK) HIP).
Qed.

End J.

(** ** The formulas [ε_I] *)

(** [⋁ l], with [⋁ [] = ⊥]. *)
Definition big_or (l : list form) : form := fold_right FOr FBot l.

Lemma val_big_or l K : val (big_or l) K <-> exists φ, In φ l /\ val φ K.
Proof.
  unfold big_or; induction l as [|φ l IH]; cbn [fold_right val In].
  - split; [intros []|intros [ψ [[] _]]].
  - rewrite IH; split.
    + intros [H|[ψ [Hψ H]]].
      * exists φ; split; [left; reflexivity|exact H].
      * exists ψ; split; [right; exact Hψ|exact H].
    + intros [ψ [[<-|Hψ] H]]; [left; exact H|right; exists ψ; split; [exact Hψ|exact H]].
Qed.

Lemma vars_in_big_or m l : (forall φ, In φ l -> vars_in m φ) -> vars_in m (big_or l).
Proof.
  unfold big_or; induction l as [|φ l IH]; intros H; cbn [fold_right vars_in];
    [constructor|split].
  - apply H; left; reflexivity.
  - apply IH; intros ψ Hψ; apply H; right; exact Hψ.
Qed.

Lemma Theta_big_or m l : (forall φ, In φ l -> Theta m φ) -> Theta m (big_or l).
Proof.
  unfold big_or; induction l as [|φ l IH]; intros H; cbn [fold_right];
    [apply Theta_bot|].
  refine (proj2 (Theta_and_or m _ _ _ _)).
  - apply H; left; reflexivity.
  - apply IH; intros ψ Hψ; apply H; right; exact Hψ.
Qed.

Lemma val_points l M : val (big_or (map FVar l)) M <-> exists i, In i l /\ M = Itv i i.
Proof.
  rewrite val_big_or; split.
  - intros [φ [Hφ H]]; apply in_map_iff in Hφ as [i [<- Hi]].
    exists i; split; [exact Hi|exact H].
  - intros [i [Hi E]]; exists (FVar i); split; [|exact E].
    apply in_map_iff; exists i; split; [reflexivity|exact Hi].
Qed.

(** [ε_I = ∼∼ ⋁_{i ∈ I} ε_i] (Lemma 3.1). *)
Definition epsI (I : interval) : form :=
  ∼ ∼ big_or (map FVar (seq (lo I) (S (hi I) - lo I))).

Lemma val_epsI I K : lo K <= hi K -> (val (epsI I) K <-> K ⊆ I).
Proof.
  intros HK; unfold epsI; cbn [val]; split.
  - intros H.
    destruct (le_gt_cases (lo I) (lo K)) as [h1|h1];
      [destruct (le_gt_cases (hi K) (hi I)) as [h2|h2]|].
    + unfold sub; lia.
    + (* the point [hi K] is in [K] but not in [I] *)
      exfalso; apply (H (Itv (hi K) (hi K))); [unfold sub; cbn; lia|].
      intros M HM HX; apply sub_point in HM; subst M.
      apply val_points in HX as [i [Hi E]]; inversion E; subst.
      apply in_seq in Hi; lia.
    + (* the point [lo K] is in [K] but not in [I] *)
      exfalso; apply (H (Itv (lo K) (lo K))); [unfold sub; cbn; lia|].
      intros M HM HX; apply sub_point in HM; subst M.
      apply val_points in HX as [i [Hi E]]; inversion E; subst.
      apply in_seq in Hi; lia.
  - intros HKI L HL HnL.
    apply (HnL (Itv (lo L) (lo L))); [unfold sub in *; cbn; lia|].
    apply val_points; exists (lo L); split; [apply in_seq; unfold sub in *; lia|reflexivity].
Qed.

Lemma Theta_epsI m I : Int m I -> Theta m (epsI I).
Proof.
  intros HI; unfold epsI; apply Theta_pneg; cbn [vars_in]; apply vars_in_big_or.
  intros φ Hφ; apply in_map_iff in Hφ as [i [<- Hi]]; apply in_seq in Hi.
  cbn [vars_in]; unfold Int in HI; lia.
Qed.

(** The intervals of [T_m]. *)
Definition ints m : list interval := subs (Itv 1 m).

Lemma in_ints m I : In I (ints m) <-> Int m I.
Proof. unfold ints; rewrite in_subs; unfold sub, Int; cbn; lia. Qed.

(** ** The isomorphism *)

Section Iso.

Variable m : nat.

(** [toΘ P = ⋁ { ε_I | J_I ≤ P }]. *)
Definition toΘf (P : Dyck (S m)) : form :=
  big_or (map epsI (filter (fun I => leDb (J m I) P) (ints m))).

Lemma Theta_toΘf P : Theta m (toΘf P).
Proof.
  apply Theta_big_or; intros φ Hφ.
  apply in_map_iff in Hφ as [I [<- HI]]; apply filter_In in HI as [HI _].
  apply Theta_epsI, in_ints, HI.
Qed.

Definition toΘ (P : Dyck (S m)) : Θ m := mkΘ (toΘf P) (Theta_toΘf P).

(** [toΘ P] is true on the intervals of [F̂_P]. *)
Lemma val_toΘ P K : Int m K -> (val (toΘ P) K <-> leD (J m K) P).
Proof.
  intros HK; cbn [fml toΘ]; unfold toΘf; rewrite val_big_or; split.
  - intros [φ [Hφ H]]; apply in_map_iff in Hφ as [I [<- HI]].
    apply filter_In in HI as [HI HIP]; apply in_ints in HI; apply leDb_spec in HIP.
    apply val_epsI in H; [|unfold Int in HK; lia].
    apply (proj2 (J_mono m K I HK HI)) in H.
    intros x; specialize (H x); specialize (HIP x); lia.
  - intros H; exists (epsI K); split.
    + apply in_map_iff; exists K; split; [reflexivity|].
      apply filter_In; split; [apply in_ints, HK|apply leDb_spec, H].
    + apply val_epsI; [unfold Int in HK; lia|exact (Int_self m K HK)].
Qed.

(** [toD φ = ⋁ { J_I | φ(I) }], Ferrari's map [f]. *)
Definition sel (φ : form) (I : interval) : bool := if val_dec φ I then true else false.

Definition toD (φ : Θ m) : Dyck (S m) :=
  fold_right joinD (hills (S m)) (map (J m) (filter (sel φ) (ints m))).

(** [F̂_(toD φ)] is the set of intervals where [φ] is true. *)
Lemma J_le_toD (φ : Θ m) K : Int m K -> (leD (J m K) (toD φ) <-> val φ K).
Proof.
  intros HK; unfold toD.
  rewrite J_le_join by first [exact HK|intros I HI; apply filter_In in HI as [HI _];
                                 apply in_ints, HI].
  split.
  - intros [I [HI HKI]]; apply filter_In in HI as [HI Hs]; apply in_ints in HI.
    unfold sel in Hs; destruct (val_dec φ I) as [Hv|]; [|discriminate Hs].
    exact (Theta_down m φ I K (fml_Theta φ) HI Hv HKI).
  - intros Hv; exists K; split; [|exact (Int_self m K HK)].
    apply filter_In; split; [apply in_ints, HK|].
    unfold sel; destruct (val_dec φ K); [reflexivity|contradiction].
Qed.

Lemma toD_toΘ P : toD (toΘ P) = P.
Proof.
  apply leD_eqE; split; apply J_embed; intros I HI H.
  - apply (val_toΘ P I HI), (J_le_toD (toΘ P) I HI), H.
  - apply (J_le_toD (toΘ P) I HI), (val_toΘ P I HI), H.
Qed.

Lemma toΘ_toD (φ : Θ m) : equiv m (toΘ (toD φ)) φ.
Proof.
  intros K HK; rewrite (val_toΘ (toD φ) K HK); exact (J_le_toD φ K HK).
Qed.

Lemma toΘ_mono P Q : leD P Q <-> toΘ P ⊢[m] toΘ Q.
Proof.
  split.
  - intros PQ K HK H; apply (val_toΘ Q K HK); apply (val_toΘ P K HK) in H.
    intros x; specialize (H x); specialize (PQ x); lia.
  - intros H; apply J_embed; intros I HI JP.
    apply (val_toΘ Q I HI); apply H; [exact HI|].
    apply (val_toΘ P I HI); exact JP.
Qed.

Lemma toΘ_bot : equiv m (toΘ (hills (S m))) ⊥.
Proof.
  intros K HK; cbn [val]; rewrite (val_toΘ _ K HK), (J_le_iff m K _ HK), h_hills_b2n.
  split; [|intros []].
  intros H; pose proof (b2n_le_1 (odd (peak_x K) && (peak_x K <? 2 * S m))).
  unfold peak_h in H; lia.
Qed.

Lemma toΘ_top : equiv m (toΘ (pyramid (S m))) ⊤.
Proof.
  intros K HK; cbn [val]; rewrite (val_toΘ _ K HK).
  split; [constructor|intros _; apply leD1].
Qed.

Lemma toΘ_meet P Q : equiv m (toΘ (meetD P Q)) (toΘ P ∧ toΘ Q).
Proof.
  intros K HK; cbn [val]; rewrite !(val_toΘ _ K HK); exact (leD_meetD P Q (J m K)).
Qed.

Lemma toΘ_join P Q : equiv m (toΘ (joinD P Q)) (toΘ P ∨ toΘ Q).
Proof.
  intros K HK; cbn [val]; rewrite !(val_toΘ _ K HK); exact (J_le_joinD m K P Q HK).
Qed.

Lemma toΘ_imp P Q : equiv m (toΘ (impD P Q)) (toΘ P ⇝ toΘ Q).
Proof.
  intros K HK; cbn [val]; rewrite (val_toΘ _ K HK), (J_le_impD m K P Q HK); split.
  - intros H L HLK HP; pose proof (Int_sub m L K HK HLK) as HL.
    apply (proj2 (val_toΘ Q L HL)), (H L HL HLK), (proj1 (val_toΘ P L HL)), HP.
  - intros H L HL HLK HLP.
    apply (proj1 (val_toΘ Q L HL)), (H L HLK), (proj2 (val_toΘ P L HL)), HLP.
Qed.

Lemma toΘ_neg P : equiv m (toΘ (impD P (hills (S m)))) (∼ toΘ P).
Proof.
  intros K HK; rewrite (toΘ_imp P (hills (S m)) K HK); cbn [val]; split.
  - intros H L HLK HP.
    exact (proj1 (toΘ_bot L (Int_sub m L K HK HLK)) (H L HLK HP)).
  - intros H L HLK HP; exfalso; exact (H L HLK HP).
Qed.

(** Theorem 3.1 *)
Theorem Dyck_Theta_iso :
  (forall P : Dyck (S m), toD (toΘ P) = P) /\
  (forall φ : Θ m, equiv m (toΘ (toD φ)) φ) /\
  (forall P Q : Dyck (S m), P ≤ Q <-> toΘ P ⊢[m] toΘ Q) /\
  equiv m (toΘ ⊥%lattice) ⊥ /\
  equiv m (toΘ ⊤%lattice) ⊤ /\
  (forall P Q : Dyck (S m), equiv m (toΘ (P ⊓ Q)) (toΘ P ∧ toΘ Q)) /\
  (forall P Q : Dyck (S m), equiv m (toΘ (P ⊔ Q)) (toΘ P ∨ toΘ Q)) /\
  (forall P Q : Dyck (S m), equiv m (toΘ (P ↛ Q)%lattice) (toΘ P ⇝ toΘ Q)) /\
  (forall P : Dyck (S m), equiv m (toΘ (¬ P)%lattice) (∼ toΘ P)).
Proof.
  split; [exact toD_toΘ|].
  split; [exact toΘ_toD|].
  split; [exact toΘ_mono|].
  split; [exact toΘ_bot|].
  split; [exact toΘ_top|].
  split; [exact toΘ_meet|].
  split; [exact toΘ_join|].
  split; [exact toΘ_imp|].
  exact toΘ_neg.
Qed.

End Iso.
