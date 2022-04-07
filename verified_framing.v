Require Import Bool List Program Arith Lia FunInd Recdef.
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


Theorem valid_communication : forall (a f k : list bool) (s : bool) (H : length k > 0), 
  a = destuff (rem_flags (add_flags (stuff a k s H) f) f) k H.
Admitted.