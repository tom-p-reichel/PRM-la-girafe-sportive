Require Export Untyped.
Require Import Lia.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Plus.
Require Import Coq.Arith.Lt.

(** (l)ift (t)erms by some (l)evel if greater or equal the (b)ound **)

Fixpoint lift (l: nat) (b: nat) (t: lterm) : lterm :=
  match t with
      | Var i as v =>  if (lt_dec i b) then v else Var (i+l)
      | App m n => App (lift l b m) (lift l b n)
      | Lam t => Lam (lift l (b+1) t)
  end.

Definition shift (b: nat) (t: lterm) : lterm :=
  lift 1 b t.

(** Substitute the variable with index [v] by [r] in the term [t] **)

Fixpoint subst (v: nat) (r: lterm) (t: lterm) : lterm :=
  match t with
      | Var i =>  match (Nat.compare i v) with
                           | Lt => Var i
                           | Eq => lift v 0 r
                           | Gt => Var (i - 1)
                  end
      | App m n => App (subst v r m) (subst v r n)
      | Lam m => Lam (subst (v+1) r m)
  end.

Lemma lift_0_ident:
  forall M, forall b,
    lift 0 b M = M.
Proof.
  induction M.
  intros. simpl. replace (n + 0) with n. case (lt_dec n b).
     reflexivity. reflexivity.
     auto.
  simpl. intros. rewrite IHM. reflexivity.
  simpl. intros. rewrite IHM1. rewrite IHM2. reflexivity.
Qed.


(** The following lemmas are described in Berghofer and Urban, who
    seem to trace down these due to Huet
*)

Lemma lift_fuse:
  forall (N: lterm) (i j n m: nat),
    i <= j <= i + m -> lift n j (lift m i N) = lift (n+m) i N.
Proof.
  induction N as [k | N1 N2 | N1].
    (* N := Var k *)
    intros. simpl. case_eq (lt_dec k i).
      (* k < i *)
      intros. simpl. assert (k < j).
          apply lt_le_trans with i. assumption. apply H.
          destruct (lt_dec k j). reflexivity. contradict H1. auto.
      (* k >= i *)
      intros. simpl.
          destruct (lt_dec (k+m) j). contradict l. lia. apply f_equal.
          lia.
    (* N := Lam .. *)
    intros. simpl. apply f_equal. rewrite N2. reflexivity. lia.
    (* N := App .. .. *)
    intros. simpl. rewrite IHN1. rewrite IHN2. auto. auto. auto.
Qed.

Lemma lift_lem2:
  forall (N L: lterm) (i j k: nat),
  k <= j -> lift i k (subst j L N) = subst (j+i) L (lift i k N).
Proof. (* This proof was automatically repaired. *)
  induction N as [v | N' | N1 ].
    (* N := Var v *)
    intros. simpl. case_eq (v ?= j).
      (* v Eq j *)
      intros. apply nat_compare_eq in H0. rewrite lift_fuse.
      destruct (lt_dec v k).
        (* v < k *)
        simpl. case_eq (v ?= j + i).
          (* Eq *)
          rewrite plus_comm. reflexivity.
          (* Lt *)
          contradict l. lia.
          (* Gt *)
          intros. apply nat_compare_gt in H1. contradict H1. lia.
        (* ~ v < k *)
        simpl. case_eq (v+i ?= j+i).
          (* Eq *)
          intros. rewrite plus_comm. reflexivity.
          (* Lt *)
          intros. apply nat_compare_lt in H1. contradict H1. lia.
          (* Gt *)
          intros. apply nat_compare_gt in H1. contradict H1. lia.
        split. lia. lia.
      (* v Lt j *)
      intros. apply nat_compare_lt in H0. destruct (lt_dec v k).
        (* v < k *)
        simpl. destruct (lt_dec v k).
          (* v < k *)
          case_eq (v ?= j + i).
            (* Eq *)
            intros. apply nat_compare_eq in H1. contradict H0. lia.
            (* Lt *)
            intros. reflexivity.
            (* Gt *)
            intros. apply nat_compare_gt in H1. contradict H1. lia.
          (* ~ v < k *)
          contradiction.
        (* ~ v < k *)
        simpl. destruct (lt_dec v k).
          (* v < k *)
          contradiction.
          (* ~ v < k *)
          case_eq (v+i ?= j+i).
            (* Eq *)
            intros. apply nat_compare_eq in H1. contradict H0. lia.
            (* Lt *)
            intros. reflexivity.
            (* Gt *)
            intros. apply nat_compare_gt in H1. contradict H0. lia.
      (* v Gt j *)
      intros. apply nat_compare_gt in H0. simpl. destruct (lt_dec (v - 1) k).
        (* v - 1 < k *)
        contradict l. lia.
        (* ~ v - 1 < k *)
        destruct (lt_dec v k).
          (* v < k *)
          contradict l. lia.
          (* ~ v < k *)
          simpl. case_eq (v+i ?= j+i).
            (* Eq *)
            intros. apply nat_compare_eq in H1. contradict H0. lia.
            (* Lt *)
            intros. apply nat_compare_lt in H1. contradict H0. lia.
            (* Gt *)
            intros. apply nat_compare_gt in H1. f_equal. lia.
    (* N := Lam N' *)
    intros. simpl. f_equal.
    assert (U: j + 1 + i = j + i + 1). lia. rewrite <- U.
    apply (IHN' L i (j+1) (k+1)). lia.
    (* N := App N1 N2 *)
    intros. simpl. f_equal.
    apply IHN1. assumption.
    apply IHN2. assumption.
Qed.

Lemma lift_lem3:
  forall (L P: lterm) (i j k: nat),
  k <= i < k + (j + 1) -> subst i P (lift (j+1) k L) = lift j k L.
Proof.
  intro L. induction L.
  intros. simpl. destruct (lt_dec n k).
    intros. simpl. assert (n < i). apply lt_le_trans with k. assumption. apply H.
    apply nat_compare_lt in H0. rewrite H0. reflexivity.

    simpl. apply not_lt in n0. assert (i < n + (j + 1)). lia.
     apply nat_compare_gt in H0. rewrite H0. apply f_equal. lia.

  intros. simpl. apply f_equal. apply IHL. lia.
  intros. simpl. rewrite IHL1. rewrite IHL2. reflexivity.
  auto. auto.
Qed.

(** We now proceed to prove the substitution lemma **)

(* variable case of the substitution lemma *)
Lemma var_subst_lemma: forall (i j n: nat), forall (N L: lterm),
   (i <= j) ->
       subst j L (subst i N (Var n)) =
                 subst i (subst (j-i) L N) (subst (j+1) L (Var n)).
Proof. (* This proof was automatically repaired. *)
  intros. simpl. case_eq (n ?= i).
  (* n = i *)
    intros. simpl. apply nat_compare_eq in H0. rewrite H0. simpl.
    assert (i < j + 1). lia. apply nat_compare_lt in H1. rewrite H1.
    simpl. assert (i = i). reflexivity. apply Nat.compare_eq_iff  in H2.
    rewrite H2. clear H1 H2. rewrite lift_lem2.
    assert (Jeq: j - i + i = j). lia. rewrite Jeq. reflexivity. lia.
  (* n < i *)
    simpl. intros. apply nat_compare_lt in H0.
    assert (n < j). lia. assert (n < j + 1). lia.
    apply nat_compare_lt in H0.
    apply nat_compare_lt in H1.
    apply nat_compare_lt in H2.
    rewrite  H1, H2. simpl. rewrite H0. reflexivity.
  (* n > i *)
    intros.
    apply nat_compare_gt in H0.
    case_eq (Nat.compare  n (j + 1)).
      (* n = j + 1 *)
      intros. apply nat_compare_eq in H1. rewrite H1.
      assert (Jeq: j + 1 - 1 = j). lia. rewrite Jeq. simpl.
      assert (HH: Nat.compare  j j = Eq ). assert (JJ: j = j). reflexivity.
          apply Nat.compare_eq_iff . assumption.
      rewrite HH. rewrite lift_lem3. reflexivity. lia.
      (* n < j + 1 *)
      intros. apply nat_compare_lt in H1. simpl.
      assert (HLt: Nat.compare  (n-1) j = Lt ).
        assert (n - 1 < j). lia. apply nat_compare_lt in H2. assumption.
        rewrite HLt.
      assert (Hgt: Nat.compare  n i = Gt).
        apply nat_compare_gt in H0. assumption.
        rewrite Hgt.
      reflexivity.
      (* n > j + 1 *)
      intros. apply nat_compare_gt in H1. simpl.
      assert (Ineq1: Nat.compare (n - 1) j = Gt).
        assert (F: n - 1 > j). lia.
        apply nat_compare_gt in F. assumption. rewrite Ineq1.
      assert (Ineq2: Nat.compare  (n - 1) i = Gt).
        assert (n - 1 > i). lia. apply nat_compare_gt in H2. assumption.
        rewrite Ineq2.
      reflexivity.
Qed.


(** The substitution lemma.
    The named version looks like this:

       [x =/= y] and [x] not free in [L] implies:
           [M[x/N][y/L] = M[y/L][x/(N[y/L])]
**)

Lemma subst_lemma: forall (M N L: lterm), forall (i j: nat),
   (i <= j) ->
       subst j L (subst i N M) = subst i (subst (j-i) L N) (subst (j+1) L M).
Proof.
  induction M.
  intros. intros. apply var_subst_lemma. assumption.
  intros. simpl. apply f_equal. rewrite IHM.
  assert (AllGood: j + 1 - (i + 1) = j - i). lia.
  rewrite AllGood. reflexivity. lia.
  intros. simpl. rewrite IHM1. rewrite IHM2. reflexivity.
  auto. auto.
Qed.

(** A few other useful lemmas about [lift] and [subst]. **)

(** Attempting to substitute a variable with index [k] in a term which is
    already shifted by [k] simply un-shifts the term: **)

Lemma subst_shift_ident:
    forall t, forall k v,
    subst k v (shift k t) =  t.
Proof. (* This proof was automatically repaired. *)
  induction t.
  unfold shift. intros.
  simpl.
  case_eq (lt_dec n k).
  intros. simpl. clear H. rewrite nat_compare_lt in l. rewrite l.
  reflexivity.
  intros. simpl.
  case_eq (Nat.compare  (n+1) k). intros. apply Nat.compare_eq_iff  in H0. lia.
  intros. apply nat_compare_lt in H0. lia.
  intros. f_equal. lia.

  intros. simpl. f_equal.
  apply IHt.

  intros. simpl. f_equal. apply IHt1. apply IHt2.
Qed.

(** Similarly, if the variable we're substituting in is [Var 0], then
    it gets unshifted even more: **)

Lemma subst_k_shift_S_k:
    forall t, forall k,
    subst k (Var 0) (shift (S k) t) = t.
Proof. (* This proof was automatically repaired. *)
  induction t.
  unfold shift. simpl.
  case_eq (lt_dec n 1).
  intros. simpl. assert (HH: n = 0). lia.
  rewrite HH. simpl.
  case_eq (lt_dec k 1).
  intros. simpl. assert (HHH: k = 0). lia.
  rewrite HHH. reflexivity.
  intros.
  case_eq (lt_dec 0 k).
  intros. simpl. destruct k.
  reflexivity. reflexivity.
  intros. lia.

  intros.
  case_eq (lt_dec n k).
  intros. simpl.
  case_eq (n ?= k).
  intros. apply Nat.compare_eq_iff  in H1. f_equal. auto.
  rewrite H1.
  case_eq (lt_dec k (S k)).
  intros. simpl. replace (Nat.compare  k k) with Eq . reflexivity.
  symmetry. apply Nat.compare_eq_iff . reflexivity.
  intros. lia. intros. apply nat_compare_lt in H1.
  case_eq (lt_dec n (S k)).
  intros. simpl.
  replace (n ?= k) with Lt . reflexivity.
  symmetry. apply nat_compare_lt. assumption.
  intros. lia. intros. apply nat_compare_gt in H1. lia.
  intros.
  case_eq (lt_dec n (S k)).
  intros. assert (n = k). lia. rewrite H2.
  simpl. replace (Nat.compare  k k) with  Eq.
  reflexivity. symmetry. apply Nat.compare_eq_iff . reflexivity.
  intros. simpl.
  replace (Nat.compare  (n+1) k) with  Gt. f_equal. lia.
  symmetry. apply nat_compare_gt. lia.


  intros. simpl. f_equal. apply IHt.

  intros. simpl. f_equal. apply IHt1. apply IHt2.
Qed.

(** Given compatible bounds, a sequence of [lift]s commutes in a very specific
    way: **)

Lemma lift_lift:
    forall M, forall b1 b2 k1 k2,
      b1 <= b2 ->
      lift k1 b1 (lift k2 b2 M) = lift k2 (k1 + b2) (lift k1 b1 M).
Proof.
  induction M.
  intros.
  simpl.
  case_eq (lt_dec n b1).
  intros.
  case_eq (lt_dec n b2).
  intros.
  simpl. rewrite H0.
  case_eq (lt_dec n (k1 + b2)).
  intros. reflexivity.
  intros. lia.
  intros. lia.

  intros.
  case_eq (lt_dec n b2).
  intros. simpl.
  rewrite H0.
  case_eq (lt_dec (n+k1) (k1+b2)).
  intros. reflexivity.
  intros. lia.
  intros. simpl.
  case_eq (lt_dec (n+k2) b1).
  intros. lia. intros.
  case_eq (lt_dec (n+k1) (k1+b2)).
  intros. lia.
  intros. f_equal. lia.

  intros.
  simpl.
  f_equal. rewrite IHM.
  f_equal. lia. lia.

  intros.
  simpl. f_equal. apply IHM1. lia.
  apply IHM2. lia.
Qed.

(** This is a reverse statement of [lift_lift]: **)

Lemma lift_lift_rev:
  forall wk k ws s t,
  k >= s + ws ->
  lift wk k (lift ws s t) = lift ws s (lift wk (k - ws) t).
Proof.
  intros.
  replace k with (ws + (k - ws)) by lia.
  rewrite <- lift_lift by lia.
  replace (ws + (k - ws) - ws) with (k - ws) by lia.
  reflexivity.
Qed.

(** [lift] distributes over [subst], also in a specific way: **)

Lemma lift_distr_subst:
  forall M N, forall v, forall i b,
    v <= b ->
    lift i b (subst v N M) = subst v (lift i (b-v) N) (lift i (b+1) M).
Proof. (* This proof was automatically repaired. *)
  induction M. intros N v.
  generalize dependent N.
  generalize dependent n.
  induction v.
  intros ? ? ? ? HH. simpl. case_eq (n ?= 0).
  intros H. apply Nat.compare_eq_iff  in H. rewrite H. simpl.
  replace (b + 1) with (S b) by lia. simpl.
  rewrite lift_0_ident. rewrite lift_0_ident.
  replace (b - 0) with b by lia. reflexivity.

  intros. simpl. apply nat_compare_lt in H. lia.
  intros. simpl. apply nat_compare_gt in H.

  assert (H1: exists n', n = (S n')).
  inversion H. exists 0. reflexivity.
  exists m. reflexivity.

  destruct H1. rewrite H0. replace (S x - 1) with x by lia.
  simpl.  replace (b +1) with (S b) by lia.
  case_eq (lt_dec x b).
  simpl.
  intros. case_eq (lt_dec (S x) (S b)).
  intros. simpl. f_equal. lia.
  intros. lia. intros.
  case_eq (lt_dec (S x) (S b)). intros. simpl. lia.
  intros. simpl. f_equal. lia.

  intros ? ? ? ? HH. simpl.
  case_eq (n ?= S  v).
  intros H. apply Nat.compare_eq_iff  in H.
  rewrite H. simpl.
  case_eq (lt_dec (S v) (b + 1)).
  intros.
  simpl. replace (v ?= v) with Eq .
  replace b with (((b - S v) + (S v))) by lia.
  rewrite lift_lift_rev. reflexivity.
  lia. symmetry. apply Nat.compare_eq_iff . reflexivity.
  intros. simpl.
  case_eq (v+i ?= v).
  intros. apply Nat.compare_eq_iff  in H1.
  assert (HHH: i = 0). lia.
  rewrite HHH. rewrite lift_0_ident.
  f_equal. rewrite lift_0_ident. reflexivity.
  intros. apply nat_compare_lt in H1.
  lia. intros. apply nat_compare_gt in H1.
  lia.
  intros.
  apply nat_compare_lt in H.
  simpl.
  case_eq (lt_dec n b).
  intros.
  case_eq (lt_dec n (b+1)).
  simpl. intros.
  replace (n ?= S  v) with Lt.
  reflexivity. symmetry. apply nat_compare_lt. assumption.
  intros. lia.
  intros. lia.
  intros. apply nat_compare_gt in H.
  simpl. case_eq (lt_dec (n - 1) b).
  intros. case_eq (lt_dec n (b+1)).
  intros. simpl. replace (Nat.compare  n (S  v)) with Gt.
  reflexivity. symmetry. apply nat_compare_gt. assumption.
  intros. lia.
  intros. case_eq (lt_dec n (b+1)). intros.
  lia. intros. simpl.
  case_eq (n+i ?= S  v).
  intros. apply Nat.compare_eq_iff  in H2.
  lia.
  intros. apply nat_compare_lt in H2.
  lia.
  intros. f_equal. lia.

  intros.
  simpl. f_equal.
  rewrite IHM. f_equal. f_equal. lia. lia.

  intros. simpl. f_equal. apply IHM1. lia.
  apply IHM2. lia.
Qed.

(** Finally, some trivialities for convenient rewriting. **)

Lemma subst_app : forall t1 t2 t3, forall n,
  subst n t3 (App t1 t2) = App (subst n t3 t1) (subst n t3 t2).
Proof. intros. reflexivity. Qed.

Lemma subst_lam : forall t t', forall n,
  subst n t' (Lam t) = Lam (subst (n+1) t' t).
Proof.  intros. reflexivity. Qed.

Lemma lift_app : forall t t' n k,
  lift n k (App t t') = App (lift n k t) (lift n k t').
Proof. intros. reflexivity. Qed.

Lemma lift_lam : forall t n k,
  lift n k (Lam t) = Lam (lift n (k+1) t).
Proof. intros. reflexivity. Qed.

