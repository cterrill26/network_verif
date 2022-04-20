Require Import Bool List Arith Lia Recdef.
Import ListNotations.


(*returns true if a starts with k, else false*)
Fixpoint starts_with (a k : list bool) : bool :=
  match a,k with
    | ha::ta, hk::tk => eqb ha hk && starts_with ta tk
    | _, [] => true
    | _, _ => false
  end.


(*returns true if a contains k, else false*)
Fixpoint contains (a k : list bool) : bool :=
  match a,k with
    | ha::ta, hk::tk => starts_with a k || contains ta k
    | _, [] => true
    | _, _ => false
  end.


(*s is stuffed after each occurance of k in a*)
Function stuff (a k : list bool) (s : bool) (H : length k > 0) {measure length a}: list bool :=
  match a with
    | [] => []
    | ha::ta => if starts_with a k then 
                  k ++ (s::(stuff (skipn (length k) a) k s H))
                else 
                  ha::(stuff ta k s H)
  end.
Proof.
  - intros. 
    rewrite skipn_length. 
    destruct (length k); simpl; lia.
  - intros. simpl. auto.
Qed.


(*after each occurance of k in a, remove the following bit*)
Function destuff (a k : list bool) (H : length k > 0) {measure length a}: list bool :=
  match a with
    | [] => []
    | ha::ta => if starts_with a k then  
                  k ++ (destuff (skipn (length k + 1) a) k H)
                else 
                  ha::(destuff ta k H)
  end.
Proof. 
  - intros. 
    rewrite skipn_length. 
    destruct (length k); simpl; lia.
  - intros. simpl. auto.
Qed.


(*after each occurance of k in a, remove the following bit*)
Function valid_message_start (a k : list bool) (s : bool) (H : length k > 0) {measure length a}: bool :=
  match a with
    | [] => true
    | ha::ta => if starts_with a k then  
                  match (skipn (length k) a) with
                    | [] => true
                    | hs::ts => eqb hs s && valid_message_start ts k s H
                  end
                else 
                 valid_message_start ta k s H
  end.
Proof. 
  - intros. 
    assert (Hlen : length (skipn (length k) (ha :: ta)) < length (ha::ta)). {
      rewrite skipn_length.
      destruct (length k); simpl; lia.
    }
    rewrite teq1 in Hlen.
    simpl.
    simpl in Hlen.
    lia. 
  - intros. simpl. auto.
Qed.


Fixpoint flag_in_data (n : nat) (f k : list bool) (s : bool) (H : length k > 0) : bool :=
  match n with
    | 0 => valid_message_start f k s H
    | S n' => valid_message_start ((firstn n k) ++ f) k s H || flag_in_data n' f k s H
  end.

Lemma t : length [true; true; true; true; true] > 0.
  simpl.
  lia.
Qed.

Lemma test : flag_in_data (length [true; true; true; true; true]) [false; true; true; true; true; true; true; false] [true; true; true; true; true] false t = false.
  repeat (simpl; try rewrite valid_message_start_equation).
  auto.
Qed.


(*flags are prepended and appended*)
Definition add_flags (a f : list bool) :=
  f ++ a ++ f.


(*returns a up until occurence of f*)
Fixpoint rem_end_flag (a f : list bool) : list bool :=
  match a with
    | [] => []
    | ha::ta => if starts_with a f then
                  []
                else
                  ha::(rem_end_flag ta f)
  end.


(*removes beginning and end flags*)
Definition rem_flags (a f : list bool) : list bool:=
  if starts_with a f then
    rem_end_flag (skipn (length f) a) f
  else
    [].


Lemma length_nil: forall A:Type, forall l:list A,
  l = nil <-> length l = 0.
Proof.
  split; intros H.
  rewrite H; simpl; auto.
  destruct l. auto.
  contradict H; simpl.
  apply sym_not_eq; apply O_S.
Qed.

Lemma nat_strong_ind: forall (P:nat -> Prop),
  P 0 -> 
  (forall n:nat, (forall (m:nat), m <= n -> P m) -> P (S n)) -> 
  forall n, P n.
Proof.
  intros P B IHs n.
  destruct n.
  exact B.
  apply IHs.
  induction n.
  intros m H; replace m with 0; try lia; exact B.
  intros m H.
  assert (m <= n \/ m = S n) as J; try lia.
  destruct J as [J|J].
  apply IHn; lia.
  rewrite J.
  apply IHs.
  apply IHn.
Qed.

Lemma length_strong_ind: forall (A:Type) (P:list A -> Prop),
  P nil -> 
  (forall (n:nat) (k:list A), (forall (l:list A), length l <= n -> P l) -> length k = S n -> P k) -> 
  forall l, P l.
Proof.
  intros A P B IH.
  assert (forall (n:nat) (l:list A), length l <= n -> P l) as G.
  intro n.
  induction n as [| n IHS] using nat_strong_ind.
  intros l H.
  assert (length l = 0) as G; try lia.
  apply length_nil in G.
  rewrite G; exact B.
  intro l.
  intro H.
  assert (length l <= n \/ length l = S n) as G; try lia.
  destruct G as [G|G].
  apply IHS with (m:=n); auto.
  apply IH with (n:=n); try exact G.
  intro k.
  apply IHS with (m:=n) (l:=k).
  auto.
  intro l.
  apply G with (n:=length l); auto.
Qed.

Lemma list_indk :
  forall (n : nat) (H : n > 0) (P : list bool -> Prop), 
  (forall (a: list bool), length a < n -> P a) ->
  (forall (ha : bool) (ta : list bool), P ta -> P (skipn n (ha::ta)) -> P (ha::ta)) ->
  forall (a : list bool), P a.
  intros n H P Hbase Hind a. 
  induction a as [| n' a IH0 IH1] using length_strong_ind.
    - assert (Hlen : length ([] : list bool) < n). {
        simpl. lia.      
      }
      apply (Hbase [] Hlen).
    - destruct a as [| ha ta].
      + simpl in IH1. lia. 
      + simpl in IH1.
        assert (talen : length ta <= n'). {
          lia.
        }
        assert (skiplen : length (skipn n (ha :: ta)) <= n'). {
          rewrite skipn_length. 
          simpl length.
          destruct n as [| n].
            + lia.
            + lia.
        }
        apply (Hind ha ta (IH0 ta talen) (IH0 (skipn n (ha :: ta)) skiplen)).
Qed.


Lemma starts_with_refl : forall (a b : list bool), 
  starts_with (a ++ b) a = true.
Proof.
  intros a.
  induction a as [| ha ta IH].
    - intros b. destruct b; simpl; auto.
    - intros b. simpl. rewrite eqb_reflx. rewrite (IH b). simpl. auto.
Qed.

Lemma starts_with_skip : forall (a k : list bool),
  starts_with a k = true ->
  k ++ skipn (length k) a = a.
Proof.
  intros a.
  induction a as [| ha ta IH].
    - intros k H. destruct k as [| hk tk].
      + simpl. auto.
      + simpl in H. lia.
    - intros k H. destruct k as [| hk tk].
      + simpl. auto.
      + simpl in H. 
        apply andb_true_iff in H.
        destruct H as [HL HR].
        rewrite <- app_comm_cons.
        simpl.
        rewrite (IH tk HR).
        rewrite (eqb_prop ha hk HL).
        auto.
Qed.

Lemma starts_with_firstn : forall (a k : list bool), 
  starts_with a k = true <-> firstn (length k) a = k.
Proof.
  split.
    - generalize dependent k.
      induction a as [| ha ta IH].
        + intros k H.
          destruct k as [| hk tk].
            * simpl. auto.
            * simpl in H. lia.
        + intros k H.
          destruct k as [| hk tk].
            * simpl. auto.
            * simpl. 
              simpl in H. 
              apply andb_true_iff in H.
              destruct H as [HL HR].
              rewrite (IH tk HR).
              rewrite (eqb_prop ha hk HL).
              auto.
    - generalize dependent k.
      induction a as [| ha ta IH].
        + intros k H.
          destruct k as [| hk tk].
            * simpl. auto.
            * simpl in H. discriminate H.
        + intros k H.
          destruct k as [| hk tk].
            * simpl. auto.
            * simpl. 
              simpl in H. 
              injection H as Heq1 Heq2.
              rewrite Heq1.
              rewrite eqb_reflx.
              simpl.
              apply (IH tk Heq2).
Qed.

Lemma not_starts_with_firstn : forall (a k : list bool), 
  starts_with a k = false <-> firstn (length k) a <> k.
Proof.
  intros.  
  pose proof (sw := starts_with_firstn a k).
  destruct sw as [swf swb].
  split.
    - intros.
      unfold not. 
      intros contra.
      pose proof (Hn := swb contra).
      rewrite Hn in H.
      lia.
    - intros.
      unfold not in H.
      destruct (starts_with a k) eqn:sw.
        + rewrite <- sw in swf at 1.
          destruct (H (swf sw)).
        + auto.
Qed. 



Lemma firstn_less : forall (a b : list bool) (n : nat), 
  firstn n a = firstn n b -> 
  firstn (n-1) a = firstn (n-1) b.
Proof.
  intros a.
  induction a as [| ha ta IH].
    - intros b n H.
      simpl.
      destruct n as [| n].
        + simpl. auto.
        + simpl.
          destruct b as [| hb tb].
            * auto.
            * simpl in H. discriminate H.
    - intros b n H.
      destruct b as [| hb tb].
        + destruct n as [| n].
          * simpl. auto.
          * simpl in H. discriminate H.
        + destruct n as [| [| n]].
          * simpl. auto.
          * simpl. auto.
          * simpl. 
            injection H as H0 H1.
            pose proof (IH' := IH tb (S n) H1). 
            simpl in IH'.
            rewrite Nat.sub_0_r in IH'.
            rewrite IH'.
            rewrite H0.
            auto.
Qed.

Lemma stuff_firstn : forall (a k : list bool) (s : bool) (H : length k > 0),
  firstn (length k) a = firstn (length k) (stuff a k s H).
  intros a.
  induction a as [| ha ta IH].
    - intros k s H.
      destruct k as [| hk tk].
        + simpl. auto.
        + rewrite stuff_equation. auto.
    - intros k s H.
      destruct k as [| hk tk].
        + simpl in H. lia.
        + destruct (starts_with (ha :: ta) (hk :: tk)) eqn:sw.
          * rewrite stuff_equation. 
            rewrite sw.
            rewrite firstn_app. 
            simpl.
            rewrite Nat.sub_diag. 
            simpl.
            simpl in sw.
            apply andb_true_iff in sw.
            destruct sw as [swl swr].
            rewrite (eqb_prop ha hk swl).
            rewrite firstn_all.
            assert (eq : firstn (length tk) ta = tk). {
              apply (starts_with_firstn ta tk).
              exact swr.
            }
            rewrite eq. 
            rewrite app_nil_r.
            auto.
          * rewrite stuff_equation. 
            rewrite sw.
            simpl.
            pose proof (IH' := firstn_less ta (stuff ta (hk :: tk) s H) (length (hk :: tk)) (IH (hk :: tk) s H)).
            simpl in IH'.
            rewrite Nat.sub_0_r in IH'.
            rewrite IH'. 
            auto.
Qed.

Lemma starts_with_stuff : forall (a k : list bool) (s : bool)  (H : length k > 0),
  starts_with a k = false ->
  starts_with (stuff a k s H) k = false.
Proof.
  intros a k s H sw.
  apply (not_starts_with_firstn (stuff a k s H) k).
  rewrite <- (stuff_firstn a k s H).
  apply (not_starts_with_firstn a k).
  exact sw.
Qed.


Lemma starts_with_short : forall (a k: list bool) ,
  length a < length k ->
  starts_with a k = false.
Proof.
  intros a.
  induction a as [| ha ta IH].
    - intros k H.
      destruct k as [| hk tk].
        + simpl in H. lia.
        + simpl. auto.
    - intros k H.
      destruct k as [| hk tk].
        + simpl in H. lia.
        + simpl in H.
          assert (Hlt : length ta < length tk). {
            lia.
          }
          simpl.
          rewrite (IH tk Hlt).
          lia.
Qed.

Lemma contains_short : forall (a k: list bool) ,
  length a < length k ->
  contains a k = false.
Proof.
  intros a k H.
  induction a as [| ha ta IH].
    - destruct k as [| hk tk].
        + simpl in H. lia.
        + simpl. auto.
    - destruct k as [| hk tk].
      + simpl in H. lia.
      + simpl. 
        simpl in H.
        assert (Hlen : length ta < length tk). {lia. }
        rewrite (starts_with_short ta tk Hlen).
        assert (Hlen' : length ta < length (hk :: tk)). {simpl. lia. }
        rewrite (IH Hlen').
        lia.
Qed.

Lemma stuff_short : forall (a k: list bool) (s : bool) (H : length k > 0),
  length a < length k ->
  stuff a k s H = a.
Proof.
  intros a k s H Hlen.
  pose proof (sw := starts_with_short a k Hlen).
  induction a as [| ha ta IH]; rewrite stuff_equation.
    - reflexivity.
    - rewrite sw.
      assert (Hlen' : length ta < length k). {
        simpl in Hlen. lia.
      }
      rewrite (IH Hlen' (starts_with_short ta k Hlen')).
      reflexivity.
Qed.

Lemma destuff_short : forall (a k: list bool) (H : length k > 0),
  length a < length k ->
  destuff a k H = a.
Proof.
  intros a k H Hlen.
  pose proof (sw := starts_with_short a k Hlen).
  induction a as [| ha ta IH]; rewrite destuff_equation.
    - reflexivity.
    - rewrite sw.
      assert (Hlen' : length ta < length k). {
        simpl in Hlen. lia.
      }
      rewrite (IH Hlen' (starts_with_short ta k Hlen')).
      reflexivity.
Qed.


Lemma valid_message_start_short : forall (a k: list bool) (s : bool) (H : length k > 0),
  length a < length k ->
  valid_message_start a k s H = true.
Proof.
  intros a k s H Hlen.
  pose proof (sw := starts_with_short a k Hlen).
  induction a as [| ha ta IH]; rewrite valid_message_start_equation.
    - reflexivity.
    - rewrite sw.
      assert (Hlen' : length ta < length k). {
        simpl in Hlen. lia.
      }
      rewrite (IH Hlen' (starts_with_short ta k Hlen')).
      reflexivity.
Qed.


Lemma stuff_destuff_eq : forall (a k: list bool) (s : bool) (H : length k > 0), 
  destuff (stuff a k s H) k H = a.
Proof.
  intros a k s H. 
  induction a as [a Hlen | ha ta Ht Hskip] using (list_indk (length k) H).
    - rewrite (stuff_short a k s H Hlen).
      rewrite (destuff_short a k H Hlen).
      reflexivity.
    - rewrite stuff_equation. 
      destruct (starts_with (ha :: ta) k) eqn:sw.
        + rewrite destuff_equation. 
          destruct (k ++ s :: stuff (skipn (length k) (ha :: ta)) k s H) eqn:l.
            * assert (len : length (k ++ s :: stuff (skipn (length k) (ha :: ta)) k s H) = 0). {
                rewrite l. simpl. auto.
              }
              rewrite app_length in len. lia.
            * rewrite <- l. 
              rewrite starts_with_refl.
              rewrite skipn_app.
              assert (lenk : length k <= (length k + 1)). {
                lia.
              }
              rewrite (skipn_all2 k lenk).
              simpl.
              assert (triv : length k + 1 - length k = 1). {
                lia.
              }
              rewrite triv.
              simpl.
              rewrite Hskip.
              apply starts_with_skip.
              apply sw.
        + pose proof (swstuff := starts_with_stuff (ha :: ta) k s H sw). 
          rewrite destuff_equation.
          rewrite stuff_equation in swstuff. 
          rewrite sw in swstuff.
          rewrite swstuff.
          rewrite Ht.
          auto.
Qed.


Lemma valid_message_start_stuff : forall (a k : list bool) (s : bool) (H : length k > 0),
  valid_message_start (stuff a k s H) k s H = true.
Proof.
  intros.
  induction a as [a Hlen | ha ta Ht Hskip] using (list_indk (length k) H).
    - rewrite (stuff_short a k s H Hlen).
      rewrite (valid_message_start_short a k s H Hlen). 
      reflexivity.
    - rewrite stuff_equation.
      destruct (starts_with (ha :: ta) k) eqn:sw.
        + rewrite valid_message_start_equation.
          destruct (k ++ s :: stuff (skipn (length k) (ha :: ta)) k s H) eqn:l.
            * assert (len : length (k ++ s :: stuff (skipn (length k) (ha :: ta)) k s H) = 0). {
                rewrite l. simpl. auto.
              }
              rewrite app_length in len. lia.
            * rewrite <- l.
              rewrite starts_with_refl.
              rewrite skipn_app.
              assert (lenk : length k <= length k). {
                lia.
              }
              rewrite (skipn_all2 k lenk).
              simpl.
              rewrite Nat.sub_diag.
              simpl.
              rewrite eqb_reflx.
              rewrite Hskip.
              auto.
        + pose proof (swstuff := starts_with_stuff (ha :: ta) k s H sw). 
          rewrite valid_message_start_equation.
          rewrite stuff_equation in swstuff. 
          rewrite sw in swstuff.
          rewrite swstuff.
          rewrite Ht.
          auto.
Qed.

Lemma no_flag_in_data_valid_message_start : forall (f k : list bool) (s : bool) (H : length k > 0) (n : nat),
  n <= length k ->  
  flag_in_data n f k s H = false ->
  (forall x, x <= n -> valid_message_start ((firstn x k) ++ f) k s H = false).
Proof.
  intros f k s H n.
  induction n as [| n' IH].
    - intros Heq Hflag x Hle. simpl. assert (triv : x = 0). {lia. } rewrite triv. simpl. simpl in Hflag. exact Hflag.
    - intros Heq Hflag x Hle.
      assert (Hle' : x < S n' \/ x = S n'). {
        lia.
      }
      clear Hle.
      destruct Hle' as [HL | HR].
        + unfold lt in HL.
          assert (HL' : x <= n'). {
            lia.
          }
          assert (Hle : n' <= length k). {lia. }
          simpl in Hflag.
          apply orb_false_iff in Hflag.
          destruct Hflag as [HflagL HflagR].
          apply (IH Hle HflagR x HL').
        + simpl in Hflag.
          rewrite HR.
          apply orb_false_iff in Hflag.
          destruct Hflag as [HflagL HflagR].
          simpl.
          exact HflagL.
Qed.

Lemma starts_with_first : forall (a f k : list bool),
  starts_with (a ++ f) k = true ->
  length a <= length k ->
  a ++ f = (firstn (length a) k) ++ f.
Proof.
  intros a f.
  induction a as [|ha ta IH].
    - simpl. auto.
    - intros k sw Hlen.
      destruct k as [| hk tk].
        + simpl in Hlen. lia.
        + simpl.
          simpl in sw.
          apply andb_true_iff in sw.
          destruct sw as [swL swR].
          assert (Hlen' : length ta <= length tk). {simpl in Hlen. lia. }
          rewrite (IH tk swR Hlen').
          rewrite (eqb_prop ha hk swL).
          auto.
Qed.


Lemma skipn_nil : forall (n : nat) (a : list bool),
  skipn n a = [] ->
  skipn (S n) a = [].
Proof.
  intros n.
  induction n as [| n' IH].
    - intros a H. destruct a as [| ha ta].
      + simpl. auto.
      + simpl in H. discriminate H.
    - intros a H. destruct a as [| ha ta].
      + simpl. auto.
      + simpl. simpl in H.
        pose proof (skip := IH ta H).
        simpl in skip.
        exact skip.
Qed.

Lemma skipn_tail : forall (n : nat) (ha hs : bool) (ta ts : list bool),
  skipn n (ha :: ta) = hs :: ts ->
  skipn n ta = ts.
Proof.
  intros n.
  induction n as [| n' IH].
    - intros. simpl. simpl in H. injection H as H0 H1. exact H1.
    - intros. 
      destruct ta as [| hta tta].
        + simpl in H. destruct n'; discriminate H.
        + simpl. simpl in H. apply (IH hta hs tta ts H). 
Qed.

Lemma skipn_skipn : forall (x y : nat) (a : list bool),
  skipn (x + y) a = skipn y (skipn x a).
Proof.
  intros x y.
  induction y as [| y' IH].
    - simpl. rewrite Nat.add_0_r. auto.
    - intros a. 
      destruct a as [| ha ta].
        + destruct x as [| x']; simpl; auto.
        + destruct x as [| x'].
          * simpl. auto.
          * rewrite Nat.add_succ_r. 
            pose proof (IH' := IH ta).
            rewrite skipn_cons at 1. 
            rewrite IH'.
            destruct (skipn (S x') (ha :: ta)) as [| hs ts] eqn:skip.
              -- simpl in skip. rewrite (skipn_nil x' ta skip). simpl. destruct y'; simpl; auto.
              -- rewrite skipn_cons. rewrite <- (skipn_tail (S x') ha hs ta ts skip). auto.
Qed.

Lemma valid_message_start_append : forall (a b k : list bool) (s : bool) (H : length k > 0),
  valid_message_start a k s H = false ->
  valid_message_start (a ++ b) k s H = false.
Proof.
Admitted.

Lemma contains_flag_invalid_short : forall (x y f k: list bool) (s : bool) (H : length k > 0),
  (forall n, n <= length k -> valid_message_start ((firstn n k) ++ f) k s H = false) ->
  length x <= length k ->
  valid_message_start (x ++ f ++ y) k s H = false.
Proof.
  intros x y f k s H Hvalid Hlen.
  induction x as [| hx tx IH].
    - pose proof (Hvalid' := Hvalid (length []) Hlen).
      simpl in Hvalid'.
      simpl.
      apply (valid_message_start_append f y k s H Hvalid').
    - destruct (starts_with ((hx :: tx) ++ f ++ y) k) eqn: sw.
        + rewrite (starts_with_first (hx :: tx) (f ++ y) k sw Hlen).
          pose proof (Hval := Hvalid (length (hx :: tx)) Hlen).
          pose proof (Hval' := valid_message_start_append ((firstn (length (hx :: tx)) k)++f) y k s H).
          rewrite <- app_assoc in Hval'.
          apply (Hval' Hval).
        + rewrite valid_message_start_equation.
          rewrite sw.
          simpl. 
          assert (Hlen' : length tx <= length k). {simpl in Hlen. lia. }
          apply (IH Hlen').
Qed.



Lemma contains_flag_invalid : forall (x y f k: list bool) (s : bool) (H : length k > 0),
  (forall n, n <= length k -> valid_message_start ((firstn n k) ++ f) k s H = false) ->
  valid_message_start (x ++ f ++ y) k s H = false.
Proof.
  intros x y f k s H Hvalid.
  assert (HlenS : length k + 1 > 0). {lia. }
  induction x as [x Hlen | hx tx Ht Hskip] using (list_indk (length k + 1) HlenS).
    - assert (Hlen' : length x <= length k). {lia. }
      apply (contains_flag_invalid_short x y f k s H Hvalid Hlen').
    - assert (triv : length (hx :: tx) <= length k \/ length (hx :: tx) > length k). {lia. }
      destruct triv as [trivL | trivR].
        + apply (contains_flag_invalid_short (hx :: tx) y f k s H Hvalid trivL).
        + rewrite valid_message_start_equation.
          destruct (starts_with ((hx :: tx) ++ f ++ y) k).
          * simpl.
            destruct (skipn (length k) (hx :: tx ++ f ++ y)) as [| hs ts] eqn:skip.
              -- rewrite app_comm_cons in skip.
                 rewrite skipn_app in skip.
                 apply app_eq_nil in skip.
                 destruct skip as [skipL skipR]. 
                 assert (Hlen : length (skipn (length k) (hx :: tx)) = 0). {rewrite skipL. simpl. auto. }
                 rewrite skipn_length in Hlen.
                 lia.
              -- replace (skipn (length k + 1) (hx :: tx) ++ f ++ y) with ts in Hskip.
                ++ rewrite Hskip. lia.
                ++ assert (Hskipeq : skipn (length k + 1) (hx :: tx ++ f ++ y) = skipn (length k + 1) (hx :: tx) ++ f ++ y). {
                     rewrite app_comm_cons.
                     rewrite skipn_app.
                     assert (Hz : length k + 1 - length (hx :: tx) = 0). {lia. }
                     rewrite Hz.
                     simpl.
                     auto.
                   } 
                   rewrite <- Hskipeq.
                   rewrite skipn_skipn.
                   rewrite skip. 
                   simpl.
                   auto.
          * simpl. exact Ht.
Qed.


Lemma starts_with_exists : forall (a k : list bool),
  starts_with a k= true ->
  exists (y : list bool), k ++ y = a.
Proof.
  intros.
  exists (skipn (length k) a).
  apply (starts_with_skip a k H).
Qed.

Lemma contains_starts_with_exists : forall (a f : list bool),
  contains a f = true ->
  exists (x y : list bool), x ++ y = a /\ starts_with y f = true.
Proof.
  intros.
  induction a as [| ha ta IH].
    - destruct f as [| hf tf].
        + exists [],[]. simpl. auto.
        + simpl in H. lia.
    - destruct f as [| hf tf].
        + exists [], (ha::ta). auto.
        + simpl in H.
          apply orb_true_iff in H.
          destruct H as [HL | HR].
            * exists [], (ha::ta). simpl. auto.
            * pose proof (IH' := IH HR).
              destruct IH' as [x [y IH']].
              exists (ha::x),y.
              simpl.
              destruct IH' as [IH'L IH'R].
              rewrite IH'L.
              auto.
Qed.


Lemma contains_exists : forall (a f : list bool),
  contains a f = true ->
  exists (x y : list bool), x ++ f ++ y = a.
  intros.
  pose proof (Hcsw := contains_starts_with_exists a f H).
  destruct Hcsw as [x [y Hcsw]].
  destruct Hcsw as [HcswL HcswR].
  exists x.
  pose proof (Hsw := starts_with_exists y f HcswR).
  destruct Hsw as [ty Heq].
  exists ty.
  rewrite Heq.
  exact HcswL.
Qed.


Lemma no_flags_in_data_proof : forall (a f k : list bool) (s : bool) (H : length k > 0),
  flag_in_data (length k) f k s H = false ->
  contains (stuff a k s H) f = false.
Proof.
  intros a f k s H Hflag.
  assert (triv : length k <= length k). {lia. }
  pose proof (Hvalid := no_flag_in_data_valid_message_start f k s H (length k) triv Hflag).
  pose proof (Hvalid' := valid_message_start_stuff a k s H).
  destruct (contains (stuff a k s H) f) eqn:eq.
    - pose proof (Hcontains := contains_exists (stuff a k s H) f eq).
      destruct Hcontains as [x [y Heq]].
      pose proof (cont := contains_flag_invalid x y f k s H Hvalid).
      rewrite Heq in cont.
      rewrite cont in Hvalid'.
      lia.
    - auto.
Qed.


Theorem valid_communication : forall (a f k : list bool) (s : bool) (H : length k > 0), 
  a = destuff (rem_flags (add_flags (stuff a k s H) f) f) k H.
Admitted.