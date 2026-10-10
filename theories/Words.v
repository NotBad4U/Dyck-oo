(** * Dyck paths as words

  Section "Ambient definitions"
  
*)
From Stdlib Require Import Arith Bool Lia List.
Import Nat.
From Dyck Require Import Dyck.
Import ListNotations EqNotations FinitePath.

(** Reading a dyck path as a [word: list step] *)
Fixpoint word {n} (P : Dyck n) : list step :=
  match P with
  | eps => []
  | ud A B => U :: word A ++ D :: word B
  end.

(* cardinality of up steps in [w] *)
Fixpoint nU (w : list step) : nat :=
  match w with [] => 0 | U :: w' => S (nU w') | D :: w' => nU w' end.

(* cardinality of down steps in [w] *)
Fixpoint nD (w : list step) : nat :=
  match w with [] => 0 | U :: w' => nD w' | D :: w' => S (nD w') end.

Lemma nU_app w1 w2 : nU (w1 ++ w2) = nU w1 + nU w2.
Proof. induction w1 as [|[] w1 IH]; simpl; lia. Qed.

Lemma nD_app w1 w2 : nD (w1 ++ w2) = nD w1 + nD w2.
Proof. induction w1 as [|[] w1 IH]; simpl; lia. Qed.

Lemma nU_nD_length w : nU w + nD w = length w.
Proof. induction w as [|[] w IH]; simpl; lia. Qed.

(** [word P] is a finite Dyck word *)

Lemma nU_word {n} (P : Dyck n) : nU (word P) = n.
Proof.
  induction P as [|m k A IHA B IHB]; simpl; [reflexivity|].
  rewrite nU_app; simpl; lia.
Qed.

Lemma nD_word {n} (P : Dyck n) : nD (word P) = n.
Proof.
  induction P as [|m k A IHA B IHB]; simpl; [reflexivity|].
  rewrite nD_app; simpl; lia.
Qed.

Lemma length_word {n} (P : Dyck n) : length (word P) = 2 * n.
Proof. rewrite <- nU_nD_length, nU_word, nD_word; lia. Qed.

(** No prefix goes below the axis. *)
Lemma word_prefix {n} (P : Dyck n) i :
  nD (firstn i (word P)) <= nU (firstn i (word P)).
Proof.
  revert i; induction P as [|m k A IHA B IHB]; intros [|i]; simpl; try lia.
  rewrite firstn_app, nD_app, nU_app.
  destruct (i - length (word A)) as [|j] eqn:E; simpl.
  - specialize (IHA i); lia.
  - rewrite firstn_all2 by lia.
    rewrite nU_word, nD_word; specialize (IHB j); lia.
Qed.

(* Another approach to define the height function than the one in Dyck.v *)
Definition height2 {n} (P : Dyck n) i := nU (firstn i (word P)) - nD (firstn i (word P)).

(* The height function defined via the word and height in Dyck.v are equal *)
Lemma height_height2 {n} (P : Dyck n) i : height P i = height2 P i.
Proof.
  unfold height2; revert i; induction P as [|m k A IHA B IHB]; intros [|j];
    try reflexivity.
  rewrite hS; cbn [word firstn nU nD].
  rewrite firstn_app, length_word.
  destruct (leb_spec j (2 * m)) as [le|gt].
  - replace (j - 2 * m) with 0 by lia; cbn [firstn]; rewrite app_nil_r.
    rewrite IHA; pose proof (word_prefix A j); lia.
  - rewrite firstn_all2 by (rewrite length_word; lia).
    replace (j - 2 * m) with (S (j - S (2 * m))) by lia; cbn [firstn].
    rewrite nU_app, nD_app, nU_word, nD_word; cbn [nU nD].
    rewrite IHB; lia.
Qed.

(** Infinite paths as words *)
Definition prefixω (P : InfinitePath.Dyckω) (n : nat) : list step := firstn n (word (InfinitePath.stage P n)).

Lemma heightω_count (P : InfinitePath.Dyckω) n :
  InfinitePath.height P n = nU (prefixω P n) - nD (prefixω P n).
Proof. apply height_height2. Qed.

Lemma prefixω_nonneg (P : InfinitePath.Dyckω) n : nD (prefixω P n) <= nU (prefixω P n).
Proof. apply word_prefix. Qed.

Definition μF := list {m & Dyck m}.

Definition push (s : step) (st : μF) : μF :=
  match s, st with
  | D, _ => existT _ 0 eps :: st
  | U, A :: B :: st' => existT _ _ (ud (projT2 A) (projT2 B)) :: st'
  | U, _ => st
  end.

Definition run (w : list step) : μF := fold_right push [existT _ 0 eps] w.

Lemma foldr_push_word {n} (P : Dyck n) st :
  fold_right push (existT _ 0 eps :: st) (word P) = existT _ n P :: st.
Proof.
  revert st; induction P as [|m k A IHA B IHB]; intros st; simpl; [reflexivity|].
  rewrite fold_right_app; simpl; rewrite IHB, IHA; reflexivity.
Qed.

Fixpoint nat_eqo (m n : nat) : option (m = n) :=
  match m, n return option (m = n) with
  | 0, 0 => Some Logic.eq_refl
  | S m', S n' => option_map (fun e => f_equal S e) (nat_eqo m' n')
  | _, _ => None
  end.

Lemma nat_eqo_refl n : nat_eqo n n = Some Logic.eq_refl.
Proof. induction n as [|n IH]; simpl; [|rewrite IH]; reflexivity. Qed.

Definition parse n (w : list step) : option (Dyck n) :=
  match run w with
  | [existT _ m P] =>
      match nat_eqo m n with
      | Some e =>
          if list_eq_dec step_eq_dec (word (rew [Dyck] e in P)) w
          then Some (rew [Dyck] e in P) else None
      | None => None
      end
  | _ => None
  end.

Lemma parse_word {n} (P : Dyck n) : parse n (word P) = Some P.
Proof.
  unfold parse, run; rewrite foldr_push_word, nat_eqo_refl; simpl.
  destruct (list_eq_dec step_eq_dec (word P) (word P)) as [_|ne];
    [reflexivity|now contradiction ne].
Qed.

Lemma parse_Some {n} w (P : Dyck n) : parse n w = Some P -> word P = w.
Proof.
  unfold parse; intros H.
  destruct (run w) as [|[m Q] [|]]; try discriminate H.
  destruct (nat_eqo m n) as [e|]; [|discriminate H].
  destruct (list_eq_dec step_eq_dec (word (rew [Dyck] e in Q)) w) as [E|];
    [|discriminate H].
  injection H as <-; exact E.
Qed.

(** The words of the μF, separated by the [D]s still waiting for their [U]. *)
Fixpoint unparse (st : μF) : list step :=
  match st with
  | [] => []
  | t :: st' =>
      word (projT2 t) ++ match st' with [] => [] | _ => D :: unparse st' end
  end.

(** A suffix [w] of a Dyck word starting at height [lv] leaves [lv + 1] trees. *)
Lemma run_ok w lv :
  lv + nU w = nD w -> (forall i, nD (firstn i w) <= lv + nU (firstn i w)) ->
  length (run w) = S lv /\ unparse (run w) = w.
Proof.
  revert lv; induction w as [|s w IH]; intros lv Hbal Hpre.
  - simpl in Hbal; replace lv with 0 by lia; split; reflexivity.
  - destruct s; simpl in Hbal.
    + (* [U]: the rest of the word starts one level higher *)
      assert (Hb : S lv + nU w = nD w) by lia.
      assert (Hp : forall i, nD (firstn i w) <= S lv + nU (firstn i w)).
      { intros i; specialize (Hpre (S i)); simpl in Hpre; lia. }
      destruct (IH (S lv) Hb Hp) as [Hsz Hun].
      change (run (U :: w)) with (push U (run w)).
      revert Hsz Hun; destruct (run w) as [|A [|B st]]; simpl; intros Hsz Hun;
        try discriminate Hsz.
      split; [lia|].
      rewrite <- Hun, <- app_assoc; reflexivity.
    + (* [D]: the rest of the word starts one level lower *)
      destruct lv as [|lv].
      { specialize (Hpre 1); simpl in Hpre; exfalso; lia. }
      assert (Hb : lv + nU w = nD w) by lia.
      assert (Hp : forall i, nD (firstn i w) <= lv + nU (firstn i w)).
      { intros i; specialize (Hpre (S i)); simpl in Hpre; lia. }
      destruct (IH lv Hb Hp) as [Hsz Hun].
      change (run (D :: w)) with (push D (run w)); simpl.
      split; [lia|].
      revert Hsz Hun; destruct (run w) as [|t st]; simpl; intros Hsz Hun;
        [discriminate Hsz|].
      now rewrite Hun.
Qed.

(** *** Dyck words of semilength [n] *)

(** [up w i] is the number of up steps among the first [i] steps of [w]. The
  height of [w] after [i] steps is [2 * up w i - i], so comparing heights is
  comparing [up]. *)
Definition up (w : list step) (i : nat) : nat := nU (firstn i w).

Definition dyck_word n (w : list step) : Prop :=
  length w = 2 * n /\ nU w = n /\
  forall i, length (firstn i w) <= 2 * up w i.

Lemma dyck_word_word {n} (P : Dyck n) : dyck_word n (word P).
Proof.
  split; [apply length_word|split; [apply nU_word|]].
  intros i; unfold up.
  pose proof (word_prefix P i); pose proof (nU_nD_length (firstn i (word P))).
  lia.
Qed.

Lemma word_parse {n} (dflt : Dyck n) w :
  dyck_word n w -> word (match parse n w with Some P => P | None => dflt end) = w.
Proof.
  intros [Hlen [HU Hpre]].
  assert (HD : nD w = n) by (pose proof (nU_nD_length w); lia).
  assert (Hp : forall i, nD (firstn i w) <= 0 + nU (firstn i w)).
  { intros i; specialize (Hpre i); pose proof (nU_nD_length (firstn i w)).
    unfold up in Hpre; lia. }
  destruct (run_ok w 0 ltac:(lia) Hp) as [Hsz Hun].
  unfold parse.
  revert Hsz Hun; destruct (run w) as [|[m P] [|]]; simpl; intros Hsz Hun;
    try discriminate Hsz.
  rewrite app_nil_r in Hun.
  assert (Hm : m = n) by (rewrite <- HU, <- Hun; symmetry; apply nU_word).
  subst m; rewrite nat_eqo_refl; simpl.
  destruct (list_eq_dec step_eq_dec (word P) w) as [_|ne];
    [exact Hun|contradiction].
Qed.

(** ** Profiles

  [up w] is the profile of [w]: it starts at [0] and each step raises it by
  [0] or [1]. A word is determined by its length and its profile. *)

Lemma up0 w : up w 0 = 0.
Proof. reflexivity. Qed.

Lemma up_nil i : up [] i = 0.
Proof. now destruct i. Qed.

Lemma up_U w i : up (U :: w) (S i) = S (up w i).
Proof. reflexivity. Qed.

Lemma up_D w i : up (D :: w) (S i) = up w i.
Proof. reflexivity. Qed.

Lemma up_app w1 w2 i : up (w1 ++ w2) i = up w1 i + up w2 (i - length w1).
Proof. unfold up; now rewrite firstn_app, nU_app. Qed.

Lemma up_all w i : length w <= i -> up w i = nU w.
Proof. intros le; unfold up; now rewrite firstn_all2. Qed.

Lemma up_lei w i : up w i <= i.
Proof.
  revert i; induction w as [|[] w IH]; intros [|i];
    rewrite ?up_nil, ?up0, ?up_U, ?up_D; try specialize (IH i); lia.
Qed.

Lemma eq_from_up w1 w2 :
  length w1 = length w2 -> (forall i, up w1 i = up w2 i) -> w1 = w2.
Proof.
  revert w2; induction w1 as [|s1 w1 IH]; intros [|s2 w2] Hlen Hup;
    simpl in Hlen; try discriminate Hlen; [reflexivity|].
  assert (Hs : s1 = s2).
  { specialize (Hup 1); destruct s1, s2; rewrite ?up_U, ?up_D, ?up0 in Hup; easy. }
  subst s2; f_equal; apply IH; [lia|].
  intros i; specialize (Hup (S i)); destruct s1; rewrite ?up_U, ?up_D in Hup; lia.
Qed.

(** *** [min] and [max] of two words computed with their heights.

  [P ∧ Q] and [P ∨ Q] are the paths whose heights are the pointwise [min]
  and [max] of [h_P] and [h_Q].  
*)

(* 
  bump U a = S a  -- one more up step read 
  bump D a = a   -- a down step doesn't change the count
*)
Definition bump (s : step) (a : nat) : nat := match s with U => S a | D => a end.

Fixpoint minw (w1 w2 : list step) (a1 a2 : nat) : list step :=
  match w1, w2 with
  | s1 :: w1', s2 :: w2' =>
      (if min a1 a2 <? min (bump s1 a1) (bump s2 a2) then U else D)
        :: minw w1' w2' (bump s1 a1) (bump s2 a2)
  | _, _ => []
  end.

Fixpoint maxw (w1 w2 : list step) (a1 a2 : nat) : list step :=
  match w1, w2 with
  | s1 :: w1', s2 :: w2' =>
      (if max a1 a2 <? max (bump s1 a1) (bump s2 a2) then U else D)
        :: maxw w1' w2' (bump s1 a1) (bump s2 a2)
  | _, _ => []
  end.

Lemma up_bump s w j : up (s :: w) (S j) = bump s (up w j).
Proof. destruct s; [apply up_U|apply up_D]. Qed.

Lemma length_minw w1 w2 a1 a2 : length w1 = length w2 -> length (minw w1 w2 a1 a2) = length w1.
Proof.
  revert w2 a1 a2; induction w1 as [|s1 w1 IH]; intros [|s2 w2] a1 a2 Hlen;
    simpl in Hlen; try discriminate Hlen; [reflexivity|].
  cbn [minw length]; f_equal; apply IH; lia.
Qed.

Lemma length_maxw w1 w2 a1 a2 : length w1 = length w2 -> length (maxw w1 w2 a1 a2) = length w1.
Proof.
  revert w2 a1 a2; induction w1 as [|s1 w1 IH]; intros [|s2 w2] a1 a2 Hlen;
    simpl in Hlen; try discriminate Hlen; [reflexivity|].
  cbn [maxw length]; f_equal; apply IH; lia.
Qed.

Lemma up_minw w1 w2 a1 a2 i : length w1 = length w2 ->
  up (minw w1 w2 a1 a2) i + min a1 a2 = min (a1 + up w1 i) (a2 + up w2 i).
Proof.
  revert w2 a1 a2 i; induction w1 as [|s1 w1 IH]; intros [|s2 w2] a1 a2 i Hlen;
    simpl in Hlen; try discriminate Hlen; cbn [minw].
  - rewrite !up_nil; lia.
  - destruct i as [|j]; [rewrite !up0; lia|].
    rewrite !up_bump; specialize (IH w2 (bump s1 a1) (bump s2 a2) j ltac:(lia)).
    destruct (ltb_spec (min a1 a2) (min (bump s1 a1) (bump s2 a2)));
      destruct s1, s2; cbn [bump] in *; lia.
Qed.

Lemma up_maxw w1 w2 a1 a2 i : length w1 = length w2 ->
  up (maxw w1 w2 a1 a2) i + max a1 a2 = max (a1 + up w1 i) (a2 + up w2 i).
Proof.
  revert w2 a1 a2 i; induction w1 as [|s1 w1 IH]; intros [|s2 w2] a1 a2 i Hlen;
    simpl in Hlen; try discriminate Hlen; cbn [maxw].
  - rewrite !up_nil; lia.
  - destruct i as [|j]; [rewrite !up0; lia|].
    rewrite !up_bump; specialize (IH w2 (bump s1 a1) (bump s2 a2) j ltac:(lia)).
    destruct (ltb_spec (max a1 a2) (max (bump s1 a1) (bump s2 a2)));
      destruct s1, s2; cbn [bump] in *; lia.
Qed.

Lemma dyck_word_minw n w1 w2 :
  dyck_word n w1 -> dyck_word n w2 -> dyck_word n (minw w1 w2 0 0).
Proof.
  intros [len1 [U1 P1]] [len2 [U2 P2]].
  assert (Hlen : length w1 = length w2) by lia.
  pose proof (length_minw w1 w2 0 0 Hlen) as Hl.
  split; [lia|split].
  - rewrite <- (up_all (minw w1 w2 0 0) (length w1)) by lia.
    pose proof (up_minw w1 w2 0 0 (length w1) Hlen) as H.
    rewrite (up_all w1 (length w1)), (up_all w2 (length w1)) in H by lia; lia.
  - intros i; pose proof (up_minw w1 w2 0 0 i Hlen).
    rewrite length_firstn, Hl.
    specialize (P1 i); specialize (P2 i); rewrite length_firstn in P1, P2; lia.
Qed.

Lemma dyck_word_maxw n w1 w2 :
  dyck_word n w1 -> dyck_word n w2 -> dyck_word n (maxw w1 w2 0 0).
Proof.
  intros [len1 [U1 P1]] [len2 [U2 P2]].
  assert (Hlen : length w1 = length w2) by lia.
  pose proof (length_maxw w1 w2 0 0 Hlen) as Hl.
  split; [lia|split].
  - rewrite <- (up_all (maxw w1 w2 0 0) (length w1)) by lia.
    pose proof (up_maxw w1 w2 0 0 (length w1) Hlen) as H.
    rewrite (up_all w1 (length w1)), (up_all w2 (length w1)) in H by lia; lia.
  - intros i; pose proof (up_maxw w1 w2 0 0 i Hlen).
    rewrite length_firstn, Hl.
    specialize (P1 i); specialize (P2 i); rewrite length_firstn in P1, P2; lia.
Qed.

Lemma up_double {n} (P : Dyck n) i : i <= 2 * n -> i <= 2 * up (word P) i.
Proof.
  intros lei; destruct (dyck_word_word P) as [Hlen [_ Hpre]].
  specialize (Hpre i); rewrite length_firstn, Hlen in Hpre; lia.
Qed.

Lemma up_word_ge {n} (P : Dyck n) i : 2 * n <= i -> up (word P) i = n.
Proof.
  intros le; rewrite up_all; [apply nU_word|].
  rewrite length_word; exact le.
Qed.

Lemma h_up {n} (P : Dyck n) i : height P i = 2 * up (word P) i - i.
Proof.
  revert i; induction P as [|m k A IHA B IHB]; intros [|j];
    rewrite ?h_eps, ?h0, ?up0; try reflexivity.
  rewrite hS; simpl word; rewrite up_U, up_app, length_word.
  destruct (leb_spec j (2 * m)) as [hj|hj].
  - replace (j - 2 * m) with 0 by lia.
    rewrite up0, IHA; pose proof (up_double A j hj); lia.
  - replace (j - 2 * m) with (S (j - S (2 * m))) by lia.
    rewrite up_D, (up_all (word A) j) by (rewrite length_word; lia).
    rewrite nU_word, IHB; lia.
Qed.

Lemma word_inj {n} (P Q : Dyck n) : word P = word Q -> P = Q.
Proof.
  intros E; apply (f_equal (parse n)) in E.
  rewrite !parse_word in E; now injection E.
Qed.

Definition eqD {n} (P Q : Dyck n) : bool :=
  if list_eq_dec step_eq_dec (word P) (word Q) then true else false.

Lemma eqD_spec {n} (P Q : Dyck n) : eqD P Q = true <-> P = Q.
Proof.
  unfold eqD; destruct (list_eq_dec step_eq_dec (word P) (word Q)) as [E|ne];
    split; intros H; try reflexivity.
  - now apply word_inj.
  - discriminate H.
  - subst Q; now contradiction ne.
Qed.

Lemma h_inj {n} (P Q : Dyck n) : (forall i, height P i = height Q i) -> P = Q.
Proof.
  intros H; apply word_inj, eq_from_up; [now rewrite !length_word|].
  intros i; destruct (le_gt_cases i (2 * n)) as [lei|lti].
  - specialize (H i); rewrite !h_up in H.
    pose proof (up_double P i lei); pose proof (up_double Q i lei); lia.
  - rewrite (up_word_ge P i), (up_word_ge Q i) by lia; reflexivity.
Qed.

Definition meetD {n} (P Q : Dyck n) : Dyck n :=
  match parse n (minw (word P) (word Q) 0 0) with Some R => R | None => P end.

Definition joinD {n} (P Q : Dyck n) : Dyck n :=
  match parse n (maxw (word P) (word Q) 0 0) with Some R => R | None => P end.

Lemma up_meetD {n} (P Q : Dyck n) i :
  up (word (meetD P Q)) i = min (up (word P) i) (up (word Q) i).
Proof.
  unfold meetD; rewrite word_parse.
  - pose proof (up_minw (word P) (word Q) 0 0 i ltac:(now rewrite !length_word)); lia.
  - apply dyck_word_minw; apply dyck_word_word.
Qed.

Lemma up_joinD {n} (P Q : Dyck n) i :
  up (word (joinD P Q)) i = max (up (word P) i) (up (word Q) i).
Proof.
  unfold joinD; rewrite word_parse.
  - pose proof (up_maxw (word P) (word Q) 0 0 i ltac:(now rewrite !length_word)); lia.
  - apply dyck_word_maxw; apply dyck_word_word.
Qed.

Lemma h_meetD {n} (P Q : Dyck n) i : height (meetD P Q) i = min (height P i) (height Q i).
Proof. rewrite !h_up, up_meetD; lia. Qed.

Lemma h_joinD {n} (P Q : Dyck n) i : height (joinD P Q) i = max (height P i) (height Q i).
Proof. rewrite !h_up, up_joinD; lia. Qed.

(** Lists all 2^k Dyck words of length k *)
Fixpoint words k : list (list step) :=
  match k with
  | 0 => [[]]
  | S k' => map (cons U) (words k') ++ map (cons D) (words k')
  end.

Lemma words_length k w : length w = k -> In w (words k).
Proof.
  revert w; induction k as [|k IH]; intros [|s w] Hlen; simpl in Hlen;
    try discriminate Hlen.
  - now left.
  - injection Hlen as Hlen; simpl; apply in_app_iff.
    destruct s; [left|right]; apply in_map_iff; exists w; split;
      [reflexivity|now apply IH| reflexivity|now apply IH].
Qed.

Lemma NoDup_map_cons s (W : list (list step)) : NoDup W -> NoDup (map (cons s) W).
Proof.
  induction 1 as [|w W nin _ IH]; simpl.
  - constructor.
  - constructor; [|exact IH].
    intros Hin; apply in_map_iff in Hin as [w' [E Hw']].
    inversion E; subst; contradiction.
Qed.

Lemma NoDup_words k : NoDup (words k).
Proof.
  induction k as [|k IH]; simpl.
  - constructor; [intros []|constructor].
  - apply NoDup_app; [now apply NoDup_map_cons|now apply NoDup_map_cons|].
    intros w Hu Hd.
    apply in_map_iff in Hu as [x [<- _]]; apply in_map_iff in Hd as [y [E _]].
    discriminate E.
Qed.

(** Dyck path as words are enumerable *)

(* Return  a list that contains every path of Dₙ *)
Definition enumD n : list (Dyck n) :=
  flat_map (fun w => match parse n w with Some P => [P] | None => [] end)
    (words (2 * n)).

(* Enumerable *)
Lemma mem_enumD {n} (P : Dyck n) : In P (enumD n).
Proof.
  apply in_flat_map; exists (word P); split.
  - apply words_length, length_word.
  - rewrite parse_word; now left.
Qed.

(* No duplicate *)
Lemma NoDup_enumD n : NoDup (enumD n).
Proof.
  unfold enumD; induction (NoDup_words (2 * n)) as [|w W nin _ IH]; simpl;
    [constructor|].
  destruct (parse n w) as [P|] eqn:E; simpl; [|exact IH].
  constructor; [|exact IH].
  intros Hin; apply in_flat_map in Hin as [w' [Hw' HP]].
  destruct (parse n w') as [P'|] eqn:E'; [|destruct HP].
  destruct HP as [eP|[]]; subst P'.
  apply parse_Some in E; apply parse_Some in E'.
  apply nin; rewrite <- E, E'; exact Hw'.
Qed.
