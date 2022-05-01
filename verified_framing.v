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


Fixpoint list_eq (a b : list bool) : bool :=
  match a, b with
    | ha::ta, hb::tb => eqb ha hb && list_eq ta tb
    | [], [] => true
    | _, _ => false
  end.

Definition lastn (n : nat) (a : list bool) : list bool :=
  rev (firstn n (rev a)). 


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



Function valid_message_start_and_end (a k : list bool) (s : bool) (H : length k > 0) {measure length a}: bool :=
  match a with
    | [] => true
    | ha::ta => if starts_with a k then  
                  match (skipn (length k) a) with
                    | [] => false
                    | hs::ts => eqb hs s && valid_message_start_and_end ts k s H
                  end
                else 
                 valid_message_start_and_end ta k s H
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

Fixpoint flag_in_data_end (n : nat) (f k : list bool) (s : bool) (H : length k > 0) : bool :=
  match n with
    | 0 => valid_message_start_and_end f k s H
    | S n' => valid_message_start_and_end ((firstn n k) ++ f) k s H || flag_in_data_end n' f k s H
  end.


Fixpoint flag_at_overlap (n : nat) (f k : list bool) (s : bool) (H : length k > 0) : bool :=
  match n with
    | 0 => false
    | S n' => list_eq (firstn n f) (lastn n f) && flag_in_data_end (length k) (firstn (length f - n) f) k s H || flag_at_overlap n' f k s H
  end.




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


Lemma list_eq_iff : forall (a b : list bool), 
  list_eq a b = true <-> a = b.
Proof.
  split.
    - generalize dependent b.
      induction a as [| ha ta IH].
        + intros.
          destruct b as [| hb tb].
            * auto.
            * simpl in H. lia.
        + intros.
          destruct b as [| hb tb].
            * simpl in H. lia.
            * simpl in H. 
              apply andb_true_iff in H.
              destruct H as [HL HR].
              apply eqb_prop in HL. 
              rewrite HL.
              rewrite (IH tb HR).
              auto.
    - generalize dependent b.
      induction a as [| ha ta IH].
        + intros.
          destruct b as [| hb tb].
            * auto.
            * simpl in H. discriminate H.
        + intros.
          destruct b as [| hb tb].
            * simpl in H. discriminate H.
            * simpl in H.
              simpl.
              injection H as H1 H2.
              apply eqb_true_iff in H1.
              rewrite H1.
              rewrite (IH tb H2).
              auto.
Qed.

Lemma list_eq_neg_iff : forall (a b : list bool), 
  list_eq a b = false <-> a <> b.
Proof.
  split.
    - unfold not.
      intros H1 H2.
      apply list_eq_iff in H2.
      rewrite H1 in H2.
      lia.
    - unfold not.
      intros.
      destruct (list_eq a b) eqn:eq.
        + apply list_eq_iff in eq.
          destruct (H eq).
        + auto.
Qed.


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

Lemma valid_message_start_le : forall (a k: list bool) (s : bool) (H : length k > 0),
  length a <= length k ->
  valid_message_start a k s H = true.
Proof.
  intros a k s H Hlen.
  assert (triv : length a < length k \/ length a = length k). {lia. }
  clear Hlen.
  destruct triv as [trivL | trivR].
    - apply (valid_message_start_short). auto.
    - induction a as [| ha ta IH].
      + simpl in trivR. lia.
      + destruct k as [| hk tk].
        * simpl in H. lia.
        * rewrite valid_message_start_equation. 
          destruct (starts_with (ha :: ta) (hk :: tk)).
            -- rewrite <- trivR. rewrite skipn_all. auto.
            -- assert (Hlen : length ta < length (hk::tk)). {simpl in trivR. simpl. lia. }
               apply (valid_message_start_short). auto.
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

Lemma no_flag_in_data_end_valid_message_start_and_end : forall (f k : list bool) (s : bool) (H : length k > 0) (n : nat),
  n <= length k ->  
  flag_in_data_end n f k s H = false ->
  (forall x, x <= n -> valid_message_start_and_end ((firstn x k) ++ f) k s H = false).
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



Lemma no_flag_at_overlap_valid_message_start_and_end : forall (f k : list bool) (s : bool) (H : length k > 0) (n : nat),
  n < length f ->  
  flag_at_overlap n f k s H = false ->
  (forall x, x > 0 -> x <= n -> firstn x f <> lastn x f \/ (forall x', x' <= length k -> valid_message_start_and_end ((firstn x' k) ++ (firstn (length f - x) f)) k s H = false)).
Proof.
  intros f k s H n.
  induction n as [| n' IH].
    - intros Hlt Hflag x Hgt Hle. lia.
    - intros Heq Hflag x Hgt Hle. 
      destruct f as [| hf tf]. 
        + simpl in Heq. lia. 
        + simpl in Hflag.
          apply orb_false_iff in Hflag.
          destruct Hflag as [HflagL HflagR].
          apply andb_false_iff in HflagL.
          assert (triv : x = S n' \/ x < S n'). {lia. }
          destruct triv as [trivL | trivR].
            * destruct HflagL as [HflagL' | HflagL'].
              -- pose proof (Hlist_eq := list_eq_neg_iff (firstn (S n') (hf :: tf)) (lastn (S n') (hf :: tf))).
                 simpl in Hlist_eq.
                 left.
                 rewrite trivL.
                 simpl.
                 destruct Hlist_eq as [Hlist_eq _].
                 apply (Hlist_eq HflagL').
              -- right.
                 assert (triv : length k <= length k). {lia. }
                 rewrite trivL.
                 simpl.
                 apply (no_flag_in_data_end_valid_message_start_and_end (firstn (length tf - n') (hf :: tf)) k s H (length k) triv HflagL').
            * assert (triv : n' < length (hf :: tf)). {lia. }
              assert (triv' : x <= n'). {lia. }
              apply (IH triv HflagR x Hgt triv').
Qed.


Lemma starts_with_same : forall (a b k : list bool),
  length a >= length k ->
  starts_with (a ++ b) k = starts_with a k.
Proof.
  intros a.
  induction a as [| ha ta IH].
    - intros b k H.
      simpl in H.
      destruct k.
        + simpl. destruct b; simpl; auto.
        + simpl in H. lia.
    - intros b k H.
      destruct k as [| hk tk].
        + simpl. auto.
        + simpl. simpl in H. 
          assert (triv : length ta >= length tk). {lia. }
          rewrite (IH b tk triv).
          auto.
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
  intros a b k s H Hvalid.
  assert (H' : length k + 1 > 0). {lia. }
  
  induction a as [a Hlen | ha ta Ht Hskip] using (list_indk (length k + 1) H').
    - assert (Hlength : length a > length k). { 
        assert (triv : length a <= length k \/ length a > length k). {lia. }  
        destruct triv as [trivL | trivR].
          - pose proof (cont := valid_message_start_le a k s H trivL). 
            rewrite cont in Hvalid.
            lia.
          - exact trivR.
      } 
      lia.
    - assert (Hlength : length (ha::ta) > length k). {
        assert (triv : length (ha::ta) <= length k \/ length (ha::ta) > length k). {lia. }  
        destruct triv as [trivL | trivR].
          - pose proof (cont := valid_message_start_le (ha::ta) k s H trivL). 
            rewrite cont in Hvalid.
            lia.
          - exact trivR.
      }
      rewrite valid_message_start_equation.
      rewrite valid_message_start_equation in Hvalid.
      assert (triv : length (ha :: ta) >= length k). {lia. }
      pose proof (Hsw := starts_with_same (ha :: ta) b k triv).
      destruct (starts_with ((ha :: ta) ++ b) k) eqn:sw.
        + rewrite <- Hsw in Hvalid.
          simpl.
          destruct (skipn (length k) (ha :: ta ++ b)) as [| hs ts] eqn:Hs.
            * rewrite app_comm_cons in Hs.
              rewrite skipn_app in Hs.
              apply app_eq_nil in Hs.
              destruct Hs as [HsL HsR].
              assert (Hlen : length (skipn (length k) (ha :: ta)) = 0). {rewrite HsL. auto. }
              rewrite skipn_length in Hlen. 
              lia.
            * destruct (skipn (length k) (ha :: ta)) as [| hsn tsn] eqn:Hsn.
                -- lia.
                -- rewrite andb_false_iff in Hvalid.
                   destruct Hvalid as [HvalidL | HvalidR].
                     ++ rewrite app_comm_cons in Hs.
                        rewrite skipn_app in Hs.
                        rewrite Hsn in Hs.
                        simpl in Hs.
                        injection Hs as Heq0 Heq1.
                        rewrite Heq0 in HvalidL.
                        rewrite HvalidL.
                        auto.
                     ++ assert (Hs' : skipn (length k + 1) (ha :: ta) = tsn). {rewrite skipn_skipn. rewrite Hsn. auto. }
                        rewrite <- Hs' in HvalidR. 
                        pose proof (Hskip' := Hskip HvalidR).
                        assert (Hs'' : skipn (length k + 1) (ha :: ta ++ b) = ts). {rewrite skipn_skipn. rewrite Hs. auto. }
                        rewrite app_comm_cons in Hs''.
                        rewrite skipn_app in Hs''.
                        assert (triv': length k + 1 - length (ha :: ta) = 0). {lia. }
                        rewrite triv' in Hs''.
                        simpl in Hs''.
                        rewrite Hs'' in Hskip'.
                        rewrite Hskip'.
                        lia.
        + rewrite <- Hsw in Hvalid.
          simpl.
          apply (Ht Hvalid).
Qed.

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
  starts_with a k = true ->
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
  contains a f = true <->
  exists (x y : list bool), x ++ f ++ y = a.
  split.
    - intros.
      pose proof (Hcsw := contains_starts_with_exists a f H).
      destruct Hcsw as [x [y Hcsw]].
      destruct Hcsw as [HcswL HcswR].
      exists x.
      pose proof (Hsw := starts_with_exists y f HcswR).
      destruct Hsw as [ty Heq].
      exists ty.
      rewrite Heq.
      exact HcswL.
    - intros.
      destruct H as [x [y H]]. 
      rewrite <- H.
      clear H. 
      induction x as [| hx tx IH].
        + simpl.
          pose proof (sw := starts_with_refl f y).
          destruct (f ++ y).
            * simpl. destruct f; auto.
            * simpl. destruct f.
              -- auto.
              -- simpl in sw. rewrite sw. auto.
        + simpl. rewrite IH. destruct f; lia. 
Qed.

Lemma contains_reverse : forall (a k : list bool), contains a k = true <-> contains (rev a) (rev k) = true.
Proof.
  split.
    - intros.
      pose proof (He := contains_exists a k).
      destruct He as [HeL HeR]. 
      pose proof (He' := HeL H).
      pose proof (Hcont := contains_exists (rev a) (rev k)).
      destruct Hcont as [HcontL HcontR].
      apply HcontR.
      destruct He' as [x [y He']].
      exists (rev y), (rev x).  
      rewrite <- He'.
      rewrite rev_app_distr.
      rewrite rev_app_distr.
      rewrite app_assoc.
      auto.
    - intros.
      pose proof (He := contains_exists (rev a) (rev k)).
      destruct He as [HeL HeR]. 
      pose proof (He' := HeL H).
      pose proof (Hcont := contains_exists a k).
      destruct Hcont as [HcontL HcontR].
      apply HcontR.
      destruct He' as [ry [rx He']].
      exists (rev rx), (rev ry).
      assert (triv : rev (ry ++ rev k ++ rx) = a). {rewrite He'. rewrite rev_involutive. auto. }
      rewrite <- triv.
      rewrite rev_app_distr.
      rewrite rev_app_distr.
      rewrite app_assoc.
      rewrite rev_involutive.
      auto.
Qed.

Lemma contains_reverse_neg : forall (a k : list bool), contains a k = false <-> contains (rev a) (rev k) = false.
Proof.
  split.
    - intros.
      destruct (contains (rev a) (rev k)) eqn:eq.
        + pose proof (cont := contains_reverse (rev a) (rev k)).
          destruct cont as [contL contR].
          pose proof (cont := contL eq).
          rewrite rev_involutive in cont.
          rewrite rev_involutive in cont.
          rewrite cont in H.
          lia.
        + auto.
    - intros.
      destruct (contains a k) eqn:eq.
        + pose proof (cont := contains_reverse a k).
          destruct cont as [contL contR].
          pose proof (cont := contL eq).
          rewrite cont in H.
          lia.
        + auto.
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
    - pose proof (Hcontains := contains_exists (stuff a k s H) f).
      destruct Hcontains as [HcontainsL HcontainsR].
      destruct (HcontainsL eq) as [x [y Heq]].
      pose proof (cont := contains_flag_invalid x y f k s H Hvalid).
      rewrite Heq in cont.
      rewrite cont in Hvalid'.
      lia.
    - auto.
Qed.

Lemma starts_with_length : forall (ha k : list bool) (ta : bool), starts_with ha k = false -> starts_with (ha ++ [ta]) k = true -> length (ha ++ [ta]) = length k.
  intros ha.
  induction ha as [| hha tha IH].
    - intros. simpl. destruct k as [| hk [| hta tk]].
      + simpl in H. lia.
      + simpl. reflexivity.
      + simpl in H0. lia. 
    - destruct k as [| hk tk].
      + intros. simpl in H. lia.
      + intros.
        simpl in H. simpl in H0. 
        apply andb_true_iff in H0. 
        destruct H0 as [H0L H0R]. 
        rewrite H0L in H. 
        simpl in H.
        simpl. 
        pose proof (IH' := IH tk ta H H0R).
        lia.
Qed.


Lemma no_flag_remove_end_flag : forall (a f : list bool) , 
  contains (a ++ removelast f) f = false -> 
  rem_end_flag (a ++ f) f = a.
Proof.
  intros.
  induction a as [| ha ta IH].
    - simpl. destruct f. 
        + simpl. auto.
        + simpl. 
          pose proof (sw_refl := starts_with_refl f []).
          rewrite app_nil_r in sw_refl.
          rewrite sw_refl.
          rewrite eqb_reflx.
          simpl. 
          auto.
    - simpl in H.
      destruct f as [| hf tf].
        + lia.
        + simpl.
          apply orb_false_iff in H.
          destruct H as [HL HR].
          rewrite (IH HR).
          apply andb_false_iff in HL.
          destruct HL as [HL | HL]. 
            * rewrite HL. simpl. auto.
            * assert (split : hf :: tf = removelast (hf :: tf) ++ [last (hf :: tf) true]). {
                apply app_removelast_last. 
                unfold not. 
                intros. 
                discriminate H.
              }
              rewrite split.
              destruct (starts_with (ta ++ removelast (hf :: tf) ++ [last (hf :: tf) true]) tf) eqn:eq.
                -- pose proof (cont := starts_with_length (ta ++ removelast (hf :: tf)) tf (last (hf :: tf) true) HL).
                   rewrite <- app_assoc in cont.
                   pose proof (cont' := cont eq).
                   rewrite app_length in cont'. 
                   rewrite app_length in cont'.
                   assert (triv : length (hf :: tf) = length (removelast (hf :: tf)) + 1). {rewrite split at 1. rewrite app_length. simpl. auto. }
                   simpl in triv.
                   simpl in cont'. 
                   lia. 
                -- rewrite andb_false_r. auto.
Qed.


Lemma no_flag_split : forall (a f : list bool) ,
  contains a f = false -> 
  contains (lastn (length f - 1) a ++ removelast f) f = false -> 
  contains (a ++ removelast f) f = false.
Proof.
  intros.
  induction a as [| ha ta IH].
    - simpl. 
      unfold lastn in H0.
      simpl in H0. 
      destruct ((length f - 1)); simpl in H0; auto.
    - assert (triv : length (ha::ta) >= length f \/ length (ha::ta) < length f). {lia. }
      destruct triv as [trivL | trivR].
        + assert (sw : starts_with ((ha :: ta) ++ removelast f) f = false). {
            assert (sw' : starts_with (ha :: ta) f = false). {
              simpl. 
              simpl in H.
              destruct f.
                * lia.
                * apply orb_false_elim in H.
                  destruct H as [HL HR].
                  auto.
            }
            rewrite starts_with_same; auto.
          }
          simpl. 
          simpl in H.
          simpl in sw.
          rewrite sw.
          destruct f as [| hf tf].
            * lia.
            * apply orb_false_iff in H.
              destruct H as [HL HR].
              rewrite orb_false_l.
              apply (IH HR). 
              apply contains_reverse_neg.
              unfold lastn.
              rewrite rev_app_distr.
              rewrite rev_involutive.
              apply contains_reverse_neg in H0.
              unfold lastn in H0.
              rewrite rev_app_distr in H0.
              rewrite rev_involutive in H0.
              enough (firstn (length (hf :: tf) - 1) (rev (ha :: ta)) = firstn (length (hf :: tf) - 1) (rev ta)). {rewrite <- H. auto. }
              replace (rev (ha :: ta)) with (rev ta ++ [ha]). { 
                rewrite firstn_app.
                assert (H : length (hf :: tf) - 1 - length (rev ta) = 0). {simpl in trivL. simpl. rewrite rev_length. lia. }
                rewrite H.
                rewrite app_nil_r.
                auto.
              }       
              auto.
        + enough (lastn (length f - 1) (ha::ta)  = (ha::ta)). {rewrite H1 in H0. auto. }
          unfold lastn. 
          assert (triv : length (rev (ha::ta)) = length (ha::ta)). {apply rev_length. }
          assert (triv' : length (rev (ha::ta)) <= (length f - 1)). {lia. }
          rewrite (firstn_all2 (rev (ha::ta)) triv').
          apply rev_involutive.
Qed.

Lemma no_flags_at_overlap_proof : forall (a f k : list bool) (s : bool) (H : length k > 0),
  length f > 0 ->  
  flag_at_overlap (length f - 1) f k s H = false ->
  contains (lastn (length f - 1) (stuff a k s H) ++ removelast f) f = false.
Proof.
  intros.
  assert (triv : length f - 1 < length f). {
    destruct f.
      - simpl in H0. lia.
      - simpl. lia.
  }
  pose proof (Hvalid := no_flag_at_overlap_valid_message_start_and_end f k s H (length f - 1) triv H1).
  
Admitted.

Lemma add_rem_flags_eq : forall (a f k : list bool) (s : bool) (H : length k > 0),
  flag_in_data (length k) f k s H = false ->
  flag_at_overlap (length f - 1) f k s H = false ->
  rem_flags (add_flags (stuff a k s H) f) f = stuff a k s H.
Proof.
  intros.
  unfold add_flags.
  unfold rem_flags.
  rewrite starts_with_refl.
  rewrite skipn_app.
  rewrite skipn_all. 
  rewrite Nat.sub_diag.
  simpl.
  assert (Hlen : length f > 0). {
    destruct f.
      - simpl in H0. 
        destruct k as [| hk tk].
          + simpl in H. lia.
          + simpl in H0.
            rewrite app_nil_r in H0. 
            rewrite firstn_all in H0.
            assert (triv : length (hk::tk) <= length (hk::tk)). {lia. }
            rewrite (valid_message_start_le (hk::tk) (hk::tk) s H triv) in H0.
            lia.
      - simpl. lia. 
  }
  pose proof (no_flag_data := no_flags_in_data_proof a f k s H H0).
  pose proof (no_flag_overlap := no_flags_at_overlap_proof a f k s H Hlen H1).
  pose proof (no_flag := no_flag_split (stuff a k s H) f no_flag_data no_flag_overlap).
  apply (no_flag_remove_end_flag (stuff a k s H) f no_flag). 
Qed.

Theorem valid_communication : forall (a f k : list bool) (s : bool) (H : length k > 0),
  flag_in_data (length k) f k s H = false ->
  flag_at_overlap (length f - 1) f k s H = false ->
  destuff (rem_flags (add_flags (stuff a k s H) f) f) k H = a.
Proof.
  intros.
  rewrite (add_rem_flags_eq a f k s H H0 H1).
  apply stuff_destuff_eq.
Qed.