(** * Dyck paths as words

  Section "Ambient definitions"
  
*)

From Stdlib Require Import Arith Bool Lia List.
Import Nat.
From Dyck Require Import Dyck.
Import ListNotations EqNotations FinitePath.

(** ** Reading a derivation as a word *)

Fixpoint word {n} (P : Dyck n) : list step :=
  match P with
  | eps => []
  | ud A B => U :: word A ++ D :: word B
  end.

(** [nU w] and [nD w] count the up and the down steps of [w]. *)
Fixpoint nU (w : list step) : nat :=
  match w with [] => 0 | U :: w' => S (nU w') | D :: w' => nU w' end.

Fixpoint nD (w : list step) : nat :=
  match w with [] => 0 | U :: w' => nD w' | D :: w' => S (nD w') end.

Lemma nU_app w1 w2 : nU (w1 ++ w2) = nU w1 + nU w2.
Proof. induction w1 as [|[] w1 IH]; simpl; lia. Qed.

Lemma nD_app w1 w2 : nD (w1 ++ w2) = nD w1 + nD w2.
Proof. induction w1 as [|[] w1 IH]; simpl; lia. Qed.

Lemma nU_nD_length w : nU w + nD w = length w.
Proof. induction w as [|[] w IH]; simpl; lia. Qed.

(** ** [word P] is a finite Dyck word *)

(** Balance: [n] up steps and [n] down steps, so the word ends on the axis. *)
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

(** No prefix dips below the axis. *)
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

(** ** The paper's height

  [height2 P i = |{j < i | p_j = u}| - |{j < i | p_j = d}|], counted on the
  first [i] steps of the word of [P]. The subtraction in [nat] is exact
  because no prefix dips below the axis ([word_prefix]). *)
Definition height2 {n} (P : Dyck n) i := nU (firstn i (word P)) - nD (firstn i (word P)).

(** [height] and [height2] agree. In [u A d B], with [A] of semilength [m]:
  the first [j ≤ 2m] steps after the opening [u] are a prefix of [A]; past
  them, [u A d] has as many [u] as [d] and the count goes on in [B]. *)
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

(** ** Parsing a word back into a derivation

  Read right to left, a word is parsed by a stack machine: [D] pushes the
  empty derivation, and [U] pops [A] then [B] and pushes [ud A B]. This is a
  right fold, so every derivation is recovered from its word ([parse_word]),
  and every Dyck word is the word of a derivation ([word_parse]). *)

Definition stack := list {m & Dyck m}.

Definition push (s : step) (st : stack) : stack :=
  match s, st with
  | D, _ => existT _ 0 eps :: st
  | U, A :: B :: st' => existT _ _ (ud (projT2 A) (projT2 B)) :: st'
  | U, _ => st
  end.

Definition run (w : list step) : stack := fold_right push [existT _ 0 eps] w.

Lemma foldr_push_word {n} (P : Dyck n) st :
  fold_right push (existT _ 0 eps :: st) (word P) = existT _ n P :: st.
Proof.
  revert st; induction P as [|m k A IHA B IHB]; intros st; simpl; [reflexivity|].
  rewrite fold_right_app; simpl; rewrite IHB, IHA; reflexivity.
Qed.

(** A semilength comparison whose proof computes, so that [parse] reduces. *)
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

(** The words of the stack, separated by the [D]s still waiting for their [U]. *)
Fixpoint unparse (st : stack) : list step :=
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

Lemma word_parse {n} (d : Dyck n) w :
  dyck_word n w -> word (match parse n w with Some P => P | None => d end) = w.
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

Lemma up_step w i : up w i <= up w (S i) <= S (up w i).
Proof.
  revert i; induction w as [|[] w IH]; intros [|i];
    rewrite ?up_nil, ?up0, ?up_U, ?up_D, ?up0; try specialize (IH i); lia.
Qed.

Lemma up_min w i : up w (min i (length w)) = up w i.
Proof.
  destruct (le_ge_cases i (length w)) as [le|le].
  - now rewrite min_l.
  - rewrite min_r by exact le.
    rewrite (up_all w (length w)), (up_all w i) by lia; reflexivity.
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

(** *** Words with a given profile *)

Section OfUp.

Variable f : nat -> nat.
Hypothesis f_step : forall i, f i <= f (S i) <= S (f i).

(** The word of length [n] whose profile, from position [i] on, follows [f]. *)
Fixpoint of_up (i n : nat) : list step :=
  match n with
  | 0 => []
  | S n' => (if f i <? f (S i) then U else D) :: of_up (S i) n'
  end.

Lemma length_of_up i n : length (of_up i n) = n.
Proof.
  revert i; induction n as [|n IH]; intros i; simpl; [reflexivity|].
  now rewrite IH.
Qed.

Lemma f_mono i j : i <= j -> f i <= f j.
Proof.
  induction j as [|j IH]; intros le.
  - replace i with 0 by lia; lia.
  - destruct (eq_dec i (S j)) as [->|ne]; [lia|].
    specialize (IH ltac:(lia)); pose proof (f_step j); lia.
Qed.

Lemma up_of_up i n j : up (of_up i n) j = f (i + min j n) - f i.
Proof.
  revert i j; induction n as [|n IH]; intros i [|j];
    try (simpl; rewrite add_0_r, sub_diag; reflexivity).
  replace (i + min (S j) (S n)) with (S i + min j n) by lia.
  pose proof (f_step i); pose proof (f_mono (S i) (S i + min j n) ltac:(lia)).
  simpl of_up; destruct (ltb_spec (f i) (f (S i))); cbv iota;
    rewrite ?up_U, ?up_D, IH; lia.
Qed.

End OfUp.

(** *** Pointwise operations on profiles

  Taking the pointwise [min] (or [max]) of two profiles gives a profile
  again, since the result still rises by [0] or [1] at each step. [opw op]
  is the word with that profile. *)

Section Pointwise.

Variable op : nat -> nat -> nat.
Hypothesis op_mono : forall a b c d, a <= c -> b <= d -> op a b <= op c d.
Hypothesis op_succ : forall a b, op (S a) (S b) = S (op a b).
Hypothesis op_sel : forall a b, op a b = a \/ op a b = b.

Definition opw (w1 w2 : list step) : list step :=
  of_up (fun i => op (up w1 i) (up w2 i)) 0 (length w1).

Lemma length_opw w1 w2 : length (opw w1 w2) = length w1.
Proof. apply length_of_up. Qed.

Lemma op_idem a : op a a = a.
Proof. now destruct (op_sel a a). Qed.

Lemma op_step w1 w2 i :
  op (up w1 i) (up w2 i) <= op (up w1 (S i)) (up w2 (S i)) <=
  S (op (up w1 i) (up w2 i)).
Proof.
  destruct (up_step w1 i), (up_step w2 i); split.
  - now apply op_mono.
  - rewrite <- op_succ; now apply op_mono.
Qed.

Lemma up_opw w1 w2 i :
  length w1 = length w2 -> up (opw w1 w2) i = op (up w1 i) (up w2 i).
Proof.
  intros Hlen; unfold opw; rewrite up_of_up by (intros k; apply op_step).
  rewrite !up0, op_idem, sub_0_r, add_0_l, up_min, Hlen, up_min.
  reflexivity.
Qed.

Lemma dyck_word_opw n w1 w2 :
  dyck_word n w1 -> dyck_word n w2 -> dyck_word n (opw w1 w2).
Proof.
  intros [len1 [U1 P1]] [len2 [U2 P2]].
  assert (Hlen : length w1 = length w2) by lia.
  split; [now rewrite length_opw|split].
  - rewrite <- (up_all (opw w1 w2) (length w1)) by (rewrite length_opw; lia).
    rewrite up_opw by exact Hlen.
    rewrite (up_all w1), (up_all w2) by lia.
    rewrite U1, U2; apply op_idem.
  - intros i; rewrite up_opw by exact Hlen.
    rewrite length_firstn, length_opw.
    specialize (P1 i); specialize (P2 i); rewrite length_firstn in P1, P2.
    destruct (op_sel (up w1 i) (up w2 i)) as [-> | ->]; lia.
Qed.

End Pointwise.

Lemma min_mono a b c d : a <= c -> b <= d -> min a b <= min c d.
Proof. intros; lia. Qed.

Lemma max_mono a b c d : a <= c -> b <= d -> max a b <= max c d.
Proof. intros; lia. Qed.

Lemma min_succ a b : min (S a) (S b) = S (min a b).
Proof. lia. Qed.

Lemma max_succ a b : max (S a) (S b) = S (max a b).
Proof. lia. Qed.

Lemma min_sel a b : min a b = a \/ min a b = b.
Proof. lia. Qed.

Lemma max_sel a b : max a b = a \/ max a b = b.
Proof. lia. Qed.

(** ** Heights are read on words *)

(** No prefix of a path dips below the axis: [2 * up ≥ i]. *)
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

(** The height after [i] steps is [2 * up - i]. *)
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

(** ** What the lattice uses *)

Lemma word_inj {n} (P Q : Dyck n) : word P = word Q -> P = Q.
Proof.
  intros E; apply (f_equal (parse n)) in E.
  rewrite !parse_word in E; now injection E.
Qed.

(** [Dyck n] has a decidable equality: compare the words. *)
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
  match parse n (opw min (word P) (word Q)) with Some R => R | None => P end.

Definition joinD {n} (P Q : Dyck n) : Dyck n :=
  match parse n (opw max (word P) (word Q)) with Some R => R | None => P end.

Lemma up_meetD {n} (P Q : Dyck n) i :
  up (word (meetD P Q)) i = min (up (word P) i) (up (word Q) i).
Proof.
  unfold meetD; rewrite word_parse.
  - apply up_opw; [exact min_mono|exact min_succ|exact min_sel|].
    now rewrite !length_word.
  - apply dyck_word_opw; [exact min_mono|exact min_succ|exact min_sel|..];
      apply dyck_word_word.
Qed.

Lemma up_joinD {n} (P Q : Dyck n) i :
  up (word (joinD P Q)) i = max (up (word P) i) (up (word Q) i).
Proof.
  unfold joinD; rewrite word_parse.
  - apply up_opw; [exact max_mono|exact max_succ|exact max_sel|].
    now rewrite !length_word.
  - apply dyck_word_opw; [exact max_mono|exact max_succ|exact max_sel|..];
      apply dyck_word_word.
Qed.

Lemma h_meetD {n} (P Q : Dyck n) i : height (meetD P Q) i = min (height P i) (height Q i).
Proof. rewrite !h_up, up_meetD; lia. Qed.

Lemma h_joinD {n} (P Q : Dyck n) i : height (joinD P Q) i = max (height P i) (height Q i).
Proof. rewrite !h_up, up_joinD; lia. Qed.

(** ** [D_n] is finite

  [enumD n] lists the paths of [D_n], each exactly once: the words of
  length [2n] that parse. *)

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

Definition enumD n : list (Dyck n) :=
  flat_map (fun w => match parse n w with Some P => [P] | None => [] end)
    (words (2 * n)).

Lemma mem_enumD {n} (P : Dyck n) : In P (enumD n).
Proof.
  apply in_flat_map; exists (word P); split.
  - apply words_length, length_word.
  - rewrite parse_word; now left.
Qed.

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
