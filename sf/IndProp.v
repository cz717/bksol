
(** * IndProp: Inductively Defined Propositions *)

Require Export Logic.

(* ####################################################### *)
(** * Inductively Defined Propositions *)

Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS : forall n : nat, ev n -> ev (S (S n)).


Fail Inductive wrong_ev (n : nat) : Prop :=
| wrong_ev_0 : wrong_ev 0
| wrong_ev_SS : forall n, wrong_ev n -> wrong_ev (S (S n)).
(* ===> Error: A parameter of an inductive type n is not
        allowed to be used as a bound variable in the type
        of its constructor. *)

Theorem ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

Theorem ev_4' : ev 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n. simpl. intros Hn.
  apply ev_SS. apply ev_SS. apply Hn.
Qed.

(** **** Exercise: 1 star (ev_double)  *)
Theorem ev_double : forall n,
  ev (double n).
Proof.
  intros. unfold double.
  induction n as [|n'].
  - apply ev_0.
  - apply ev_SS. apply IHn'.
Qed.
(** [] *)

(* ####################################################### *)
(** * Using Evidence in Proofs *)

(** ** Inversion on Evidence *)

Theorem evenb_minus2: forall n,
  evenb n = true -> evenb (pred (pred n)) = true.
Proof.
  intros [ | [ | n' ] ].
  - (* n = 0 *) reflexivity.
  - (* n = 1; contradiction *) intros H. inversion H.
  - (* n = n' + 2 *) simpl. intros H. apply H.
Qed.

Theorem ev_minus2: forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros [ | [ | n' ] ].
  - (* n = 0 *) simpl. intros _. apply ev_0.
  - (* n = 1; we're stuck! *) simpl.
Abort.

Theorem ev_minus2 : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  inversion E as [| n' E'].
  - (* E = ev_0 *) simpl. apply ev_0.
  - (* E = ev_SS n' E' *) simpl. apply E'.  Qed.

Theorem ev_minus2' : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  destruct E as [| n' E'].
  - (* E = ev_0 *) simpl. apply ev_0.
  - (* E = ev_SS n' E' *) simpl. apply E'.  Qed.

Theorem evSS_ev : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.
  destruct E as [| n' E'].
  - (* E = ev_0. *)
    (* We must prove that [n] is even from no assumptions! *)
Abort.

Theorem evSS_ev : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.
  inversion E as [| n' E'].
  (* We are in the [E = ev_SS n' E'] case now. *)
  apply E'.
Qed.

Theorem one_not_even : ~ ev 1.
Proof.
  intros H. inversion H. Qed.


(** **** Exercise: 1 star (inversion_practice)  *)
(** Prove the following results using [inversion]. *)

Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros. 
  inversion H. inversion H1. apply H3. 
Qed.

Theorem even5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  intros. exfalso.
  inversion H. inversion H1. inversion H3.
Qed.
(** [] *)


(* ####################################################### *)
(** ** Induction on Evidence *)


Lemma ev_even : forall n,
  ev n -> exists k, n = double k.
Proof.
  intros n E. inversion E as [| n' E'].
  - (* E = ev_0 *)
    exists 0. reflexivity.
  - (* E = ev_SS n' E' *) simpl.
Abort.

Lemma ev_even : forall n,
  ev n -> exists k, n = double k.
Proof.
  intros n E.
  induction E as [|n' E' IH].
  - (* E = ev_0 *)
    exists 0. reflexivity.
  - (* E = ev_SS n' E'
       with IH : exists k', n' = double k' *)
    destruct IH as [k' Hk'].
    rewrite Hk'. exists (S k'). reflexivity.
Qed.


Theorem ev_even_iff : forall n,
  ev n <-> exists k, n = double k.
Proof.
  intros n. split.
  - (* -> *) apply ev_even.
  - (* <- *) intros [k Hk]. rewrite Hk. apply ev_double.
Qed.



(** **** Exercise: 2 stars (ev_sum)  *)
Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros n m N M.
  induction N as [|n' N'].
  - apply M.
  - simpl. apply ev_SS. apply IHN'.
Qed.
(** [] *)

(** **** Exercise: 4 stars, advanced (ev_alternate)  *)
(** In general, there may be multiple ways of defining a
    property inductively.  For example, here's a (slightly contrived)
    alternative definition for [ev]: *)

Inductive ev' : nat -> Prop :=
| ev'_0 : ev' 0
| ev'_2 : ev' 2
| ev'_sum : forall n m, ev' n -> ev' m -> ev' (n + m).

(** Prove that this definition is logically equivalent to
    the old one. *)

Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
  intros n. split. 
  - intros E. induction E as [ | | n' m' N' N M' M].
    + apply ev_0.
    + apply ev_SS. apply ev_0.
    + apply ev_sum. apply N. apply M.
  - intros E. induction E as [ | n' N'].
    + apply ev'_0.
    + simpl. apply (ev'_sum 2).
      * apply ev'_2.
      * apply IHN'.
Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced, recommended (ev_ev__ev)  *)
(** Finding the appropriate thing to do induction on is a
    bit tricky here: *)

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  intros n m NM N.
  induction N as [|n' N'].
  - apply NM.
  - apply IHN'.
    simpl in NM. inversion NM.
    apply H0.
Qed.
(** [] *)

(** **** Exercise: 3 stars, optional (ev_plus_plus)  *)
(** This exercise just requires applying existing lemmas.  No
    induction or even case analysis is needed, though some of the
    rewriting may be tedious. *)

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros n m p NM NP.
  apply ev_ev__ev with (n:=(n+n)).
  - rewrite <- plus_assoc.
    rewrite plus_assoc with (m:=m).
    rewrite plus_comm.
    rewrite <- plus_assoc.
    rewrite plus_comm with (n:= p).
    apply ev_sum. apply NM. apply NP.
  - assert (H: forall x, ev (x + x)).
    { induction x as [|x'].
      - apply ev_0.
      - simpl. rewrite <- plus_n_Sm.
        apply ev_SS. apply IHx'. }
    apply H.
Qed.
(** [] *)

(* ####################################################### *)
(** * Inductive Relations *)

    
Module LeModule.

Inductive le : nat -> nat -> Prop :=
  | le_n : forall n, le n n
  | le_S : forall n m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).

Theorem test_le1 :
  3 <= 3.
Proof.
  (* WORKED IN CLASS *)
  apply le_n.  Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  (* WORKED IN CLASS *)
  apply le_S. apply le_S. apply le_S. apply le_n.  Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof.
  (* WORKED IN CLASS *)
  intros H. inversion H. inversion H2.  Qed.


End LeModule.

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

Inductive square_of : nat -> nat -> Prop :=
  sq : forall n:nat, square_of n (n * n).

Inductive next_nat : nat -> nat -> Prop :=
  | nn : forall n:nat, next_nat n (S n).

Inductive next_even : nat -> nat -> Prop :=
  | ne_1 : forall n, ev (S n) -> next_even n (S n)
  | ne_2 : forall n, ev (S (S n)) -> next_even n (S (S n)).

(** **** Exercise: 2 stars, recommended (total_relation)  *)
(** Define an inductive binary relation [total_relation] that holds
    between every pair of natural numbers. *)

Inductive total_relation : nat -> nat -> Prop :=
  | tr : forall n m, total_relation n m.

(** [] *)

(** **** Exercise: 2 stars (empty_relation)  *)
(** Define an inductive binary relation [empty_relation] (on numbers)
    that never holds. *)

Inductive empty_relation : nat -> nat -> Prop := .

(** [] *)

(** **** Exercise: 3 stars, optional (le_exercises)  *)
(** Here are a number of facts about the [<=] and [<] relations that
    we are going to need later in the course.  The proofs make good
    practice exercises. *)

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros m n o mn.
  induction mn as [ | n' mn' IH ].
  - trivial.
  - intros no. apply IH.
    induction no as [ | o' no' IH' ].
    + apply le_S. apply le_n.
    + apply le_S. apply IH'.
      intros n'o'. 
      
Admitted.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  induction n as [|n'].
  - trivial.
  - apply le_S. apply IHn'.
Qed.


Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros n m nm.
  induction nm as [ | m' nm' IH].
  - trivial.
  - apply le_S. apply IH.
Qed. 


Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros n m S.
  induction S as [ E | ].
  
Admitted.


Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intros a b.
  induction b as [|b'].
  - rewrite <- plus_n_O. trivial.
  - rewrite <- plus_n_Sm. apply le_S. apply IHb'.
Qed.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
 unfold lt. intros n1 n2 m H. split.
 - apply le_trans with (n:= S n1 + n2).
   + apply le_plus_l.
   + simpl. apply H.
 - apply le_trans with (n := S n2 + n1).
   + apply le_plus_l.
   + simpl. rewrite plus_comm. apply H.
Qed.


Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  unfold lt. intros n m H.
  apply le_S. apply H.
Qed.


Theorem leb_complete : forall n m,
  leb n m = true -> n <= m.
Proof.
  induction n as [| n' ].
  - (* n = 0 *)
    intros m H.  apply O_le_n.
  - (* n = S n' *)
    induction m as [| m' ].
    + intros H. inversion H.
    + intros H. apply n_le_m__Sn_le_Sm.
      apply IHn'. simpl in H. apply H.
Qed.


Theorem leb_correct : forall n m,
  n <= m ->
  leb n m = true.
Proof.
  intros n m. 
  generalize dependent n.
  induction m as [|m'].
  - intros n H.
    inversion H. trivial.
  - intros n H.
    destruct n as [|n'].
    + trivial.
    + simpl. apply IHm'.
      apply Sn_le_Sm__n_le_m. apply H.
Qed.


Theorem leb_true_trans : forall n m o,
  leb n m = true -> leb m o = true -> leb n o = true.
Proof.
  intros n m o nm mo.
  apply leb_correct.
  apply le_trans with (n := m);
  apply leb_complete; assumption.
Qed.


(** **** Exercise: 2 stars, optional (leb_iff)  *)
Theorem leb_iff : forall n m,
  leb n m = true <-> n <= m.
Proof.
  split. 
  apply leb_complete. 
  apply leb_correct.
Qed.
(** [] *)

Module R.

(** **** Exercise: 3 stars, recommended (R_provability2)  *)
(** We can define three-place relations, four-place relations,
    etc., in just the same way as binary relations.  For example,
    consider the following three-place relation on numbers: *)

Inductive R : nat -> nat -> nat -> Prop :=
   | c1 : R 0 0 0
   | c2 : forall m n o, R m n o -> R (S m) n (S o)
   | c3 : forall m n o, R m n o -> R m (S n) (S o)
   | c4 : forall m n o, R (S m) (S n) (S (S o)) -> R m n o
   | c5 : forall m n o, R m n o -> R n m o.

(** - Which of the following propositions are provable?
      - [R 1 1 2]
      - [R 2 2 6]

    - If we dropped constructor [c5] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.

    - If we dropped constructor [c4] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.

(* FILL IN HERE *)
[]
*)

(** **** Exercise: 3 stars, optional (R_fact)  *)
(** The relation [R] above actually encodes a familiar function.
    Figure out which function; then state and prove this equivalence
    in Coq? *)

Definition fR : nat -> nat -> nat :=
  plus.

Theorem R_equiv_fR : forall m n o, R m n o <-> fR m n = o.
Proof.
  intros m n o. unfold fR. split.
  - (* -> *)
    intros H. 
    induction H.
    + trivial.
    + simpl. rewrite IHR. reflexivity.
    + simpl. rewrite <- plus_n_Sm. 
      rewrite IHR. reflexivity.
    + simpl in IHR. rewrite <- plus_n_Sm in IHR.
      inversion IHR. reflexivity.
    + rewrite plus_comm. apply IHR.
  - generalize dependent o.
    generalize dependent n.
    generalize dependent m.
    induction m as [|m'].
    + induction n as [|n'].
      * intros o H. simpl in H. rewrite <- H. apply c1.
      * intros o H. simpl in H. rewrite <- H. 
        apply c3. apply IHn'. reflexivity.
    + induction n as [|n']. 
      * intros o H. rewrite <- plus_n_O in H. 
        rewrite <- H. apply c2.
        apply IHm'. rewrite plus_n_O. reflexivity.
      * intros o H. simpl in H. rewrite <- plus_n_Sm in H.
        rewrite <- H. apply c3. apply IHn'. reflexivity.
Qed.
(** [] *)

End R.

(** **** Exercise: 4 stars, advanced (subsequence)  *)
(** A list is a _subsequence_ of another list if all of the elements
    in the first list occur in the same order in the second list,
    possibly with some extra elements in between. For example,
    [1;2;3]
    is a subsequence of each of the lists
    [1;2;3]
    [1;1;1;2;2;3]
    [1;2;7;3]
    [5;6;1;9;9;2;7;3;8]
    but it is _not_ a subsequence of any of the lists
    [1;2]
    [1;3]
    [5;6;2;1;7;3;8]

    - Define an inductive proposition [subseq] on [list nat] that
      captures what it means to be a subsequence. (Hint: You'll need
      three cases.)

    - Prove [subseq_refl] that subsequence is reflexive, that is,
      any list is a subsequence of itself.

    - Prove [subseq_app] that for any lists [l1], [l2], and [l3],
      if [l1] is a subsequence of [l2], then [l1] is also a subsequence
      of [l2 ++ l3].

    - (Optional, harder) Prove [subseq_trans] that subsequence is
      transitive -- that is, if [l1] is a subsequence of [l2] and [l2]
      is a subsequence of [l3], then [l1] is a subsequence of [l3].
      Hint: choose your induction carefully!
*)

Inductive subseq : list nat -> list nat -> Prop :=
  | c1: forall x: list nat, subseq [] x
  | c2: forall x1 h x2, subseq x1 x2 -> subseq x1 (h::x2)
  | c3: forall h t x, subseq t x -> subseq (h::t) (h::x).

Theorem subseq_refl : forall x : list nat,  subseq x x.
Proof.
  intros x. induction x as [|h t].
  - apply c1.
  - apply c3. apply IHt.
Qed.

Theorem subseq_app : 
  forall l1 l2 l3, subseq l1 l2 -> subseq l1 (l2++l3).
Proof.
  intros l1 l2 l3. 
  generalize dependent l1.
  induction l2 as [|h t].
  - intros l1 H. inversion H. apply c1.
  - intros l1 H. inversion H.
    + apply c1.
    + simpl. apply c2. apply IHt. apply H2.
    + simpl. apply c3. apply IHt. apply H2.
Qed.
(** [] *)

(** **** Exercise: 2 stars, optional (R_provability)  *)
(** Suppose we give Coq the following definition:
    Inductive R : nat -> list nat -> Prop :=
      | c1 : R 0 []
      | c2 : forall n l, R n l -> R (S n) (n :: l)
      | c3 : forall n l, R (S n) l -> R n l.
    Which of the following propositions are provable?

    - [R 2 [1;0]]
    - [R 1 [1;2;1;0]]
    - [R 6 [3;2;1;0]]
*)

(** [] *)


(* ############################################################ *)
(** * Case Study: Regular Expressions *)

Inductive reg_exp (T : Type) : Type :=
| EmptySet : reg_exp T
| EmptyStr : reg_exp T
| Char : T -> reg_exp T
| App : reg_exp T -> reg_exp T -> reg_exp T
| Union : reg_exp T -> reg_exp T -> reg_exp T
| Star : reg_exp T -> reg_exp T.

Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.


Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
| MEmpty : exp_match [] EmptyStr
| MChar : forall x, exp_match [x] (Char x)
| MApp : forall s1 re1 s2 re2,
           exp_match s1 re1 ->
           exp_match s2 re2 ->
           exp_match (s1 ++ s2) (App re1 re2)
| MUnionL : forall s1 re1 re2,
              exp_match s1 re1 ->
              exp_match s1 (Union re1 re2)
| MUnionR : forall re1 s2 re2,
              exp_match s2 re2 ->
              exp_match s2 (Union re1 re2)
| MStar0 : forall re, exp_match [] (Star re)
| MStarApp : forall s1 s2 re,
               exp_match s1 re ->
               exp_match s2 (Star re) ->
               exp_match (s1 ++ s2) (Star re).



Notation "s =~ re" := (exp_match s re) (at level 80).


(* ############################################################ *)

Example reg_exp_ex1 : [1] =~ Char 1.
Proof.
  apply MChar.
Qed.

Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1] _ [2]).
  - apply MChar.
  - apply MChar.
Qed.

Example reg_exp_ex3 : ~ ([1; 2] =~ Char 1).
Proof.
  intros H. inversion H.
Qed.

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.

Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
  simpl. apply (MApp [1]).
  { apply MChar. }
  apply (MApp [2]).
  { apply MChar. }
  apply (MApp [3]).
  { apply MChar. }
  apply MEmpty.
Qed.


Lemma MStar1 :
  forall T s (re : reg_exp T) ,
    s =~ re ->
    s =~ Star re.
Proof.
  intros T s re H.
  rewrite <- (app_nil_r _ s).
  apply (MStarApp s [] re).
  - apply H.
  - apply MStar0.
Qed.


(** **** Exercise: 3 stars (exp_match_ex1)  *)
(** The following lemmas show that the informal matching rules given
    at the beginning of the chapter can be obtained from the formal
    inductive definition. *)

Lemma empty_is_empty : forall T (s : list T),
  ~ (s =~ EmptySet).
Proof.
  intros T s H.
  inversion H.
Qed.

Lemma MUnion' : forall T (s : list T) (re1 re2 : reg_exp T),
  s =~ re1 \/ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
  intros T s re1 re2.
  intros [ H | H ].
  - apply MUnionL. apply H.
  - apply MUnionR. apply H.
Qed.

(** The next lemma is stated in terms of the [fold] function from the
    [Poly] chapter: If [ss : list (list T)] represents a sequence of
    strings [s1, ..., sn], then [fold app ss []] is the result of
    concatenating them all together. *)

Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp T),
  (forall s, In s ss -> s =~ re) ->
  fold app ss [] =~ Star re.
Proof.
  intros T ss re H.
  induction ss as [|h t].
  - simpl. apply MStar0.
  - simpl. apply MStarApp.
    + apply H. simpl. left. trivial.
    + apply IHt. intros s H'.
      apply H. simpl. right. apply H'.
Qed.
(** [] *)

(** **** Exercise: 4 stars (reg_exp_of_list)  *)
(** Prove that [reg_exp_of_list] satisfies the following
    specification: *)

Lemma reg_exp_of_list_spec : forall T (s1 s2 : list T),
  s1 =~ reg_exp_of_list s2 <-> s1 = s2.
Proof.
  intros T s1 s2. 
  generalize dependent s1.
  induction s2 as [|h t].
  - (* s2 = [] *)
    split. 
    + intros H. simpl in H. inversion H. reflexivity.
    + intros H. simpl. rewrite H. apply MEmpty.
  - (* s2 = h::t *)
    intros s1. split. 
    + intros H. simpl in H. inversion H. 
      inversion H3. simpl. 
      rewrite (IHt s2) in H4. rewrite H4. reflexivity.
    + intros H. simpl. rewrite H.
      assert ( A : forall S (x:S) y, [x]++y = x::y).
      {  intros S x y. simpl. reflexivity.  }
      rewrite <- A. apply MApp.
      * apply MChar.
      * apply IHt. reflexivity.
Qed.

(** [] *)

Fixpoint re_chars {T} (re : reg_exp T) : list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.

Theorem in_re_match : forall T (s : list T) (re : reg_exp T) (x : T),
  s =~ re ->
  In x s ->
  In x (re_chars re).
Proof.
  intros T s re x Hmatch Hin.
  induction Hmatch
    as [
        |x'
        |s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2 re2 Hmatch IH
        |re|s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  (* WORKED IN CLASS *)
  - (* MEmpty *)
    apply Hin.
  - (* MChar *)
    apply Hin.
  - simpl. rewrite in_app_iff in *.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      left. apply (IH1 Hin).
    + (* In x s2 *)
      right. apply (IH2 Hin).
  - (* MUnionL *)
    simpl. rewrite in_app_iff.
    left. apply (IH Hin).
  - (* MUnionR *)
    simpl. rewrite in_app_iff.
    right. apply (IH Hin).
  - (* MStar0 *)
    destruct Hin.
  - (* MStarApp *)
    simpl. rewrite in_app_iff in Hin.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      apply (IH1 Hin).
    + (* In x s2 *)
      apply (IH2 Hin).
Qed.

(** **** Exercise: 4 stars (re_not_empty)  *)
(** Write a recursive function [re_not_empty] that tests whether a
    regular expression matches some string. Prove that your function
    is correct. *)

Fixpoint re_not_empty {T} (re : reg_exp T) : bool :=
  match re with
    | EmptySet => false
    | EmptyStr => true
    | Char _ => true
    | App re1 re2 => andb (re_not_empty re1) (re_not_empty re2)
    | Union re1 re2 => orb (re_not_empty re1) (re_not_empty re2)
    | Star re1 => true
  end.

Lemma re_not_empty_correct : forall T (re : reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  intros T re.  split.
  - (* -> *)
    intros [s Hmatch].
    induction Hmatch
    as [
        |x'
        |s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2 re2 Hmatch IH
        |re|s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
    + (* EmptyStr *)
      trivial.
    + (* Char *)
      trivial.
    + (* App *)
      simpl. rewrite IH1. rewrite IH2. trivial.
    + (* Union *)
      simpl. rewrite IH. trivial.
    + (* Union *)
      simpl. rewrite IH. 
      destruct (re_not_empty re1);trivial.
    + (* Star *)
      trivial.
    + (* Star *)
      trivial.
  - (* <- *)
    intros H. 
    induction re.
    + (* EmptySet *)
      inversion H.
    + (* EmptyStr *)
      exists []. apply MEmpty.
    + (* Char *)
      exists [t]. apply MChar.
    + (* App *)
      simpl in H. 
      rewrite andb_true_iff in H.
      destruct H as [L R].
      destruct (IHre1 L) as [s1 H1].
      destruct (IHre2 R) as [s2 H2].
      exists (s1++s2). apply MApp; assumption.
    + (* union *)
      simpl in H. rewrite orb_true_iff in H.
      destruct H as [H | H].
      * destruct (IHre1 H) as [s1 M].
        exists s1. apply MUnionL. assumption.
      * destruct (IHre2 H) as [s2 M].
        exists s2. apply MUnionR. assumption.
    + (* Star *)
      exists []. apply MStar0.
Qed.

(** [] *)

(** ** The [remember] Tactic *)

Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].
  - (* MEmpty *)
    simpl. intros H. apply H.
  - (* MChar. Stuck... *)
Abort.

Lemma star_app: forall T (s1 s2 : list T) (re re' : reg_exp T),
  s1 =~ re' ->
  re' = Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Abort.

Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re'.
  generalize dependent s2.
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].

  - (* MEmpty *)  inversion Heqre'.
  - (* MChar *)   inversion Heqre'.
  - (* MApp *)    inversion Heqre'.
  - (* MUnionL *) inversion Heqre'.
  - (* MUnionR *) inversion Heqre'.
  - (* MStar0 *)
    inversion Heqre'. intros s H. apply H.
  - (* MStarApp *)
    inversion Heqre'. rewrite H0 in IH2, Hmatch1.
    intros s2 H1. rewrite <- app_assoc.
    apply MStarApp.
    + apply Hmatch1.
    + apply IH2.
      * reflexivity.
      * apply H1.
Qed.

(** **** Exercise: 4 stars (exp_match_ex2)  *)

(** The [MStar''] lemma below (combined with its converse, the
    [MStar'] exercise above), shows that our definition of [exp_match]
    for [Star] is equivalent to the informal one given previously. *)

Lemma MStar'' : forall T (s : list T) (re : reg_exp T),
  s =~ Star re ->
  exists ss : list (list T),
    s = fold app ss []
    /\ forall s', In s' ss -> s' =~ re.
Proof.
  intros T s re H.
  remember (Star re) as re'.
  induction H
    as [|x'|s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2 re2 Hmatch IH
        |re''|s1 s2 re'' Hmatch1 IH1 Hmatch2 IH2].
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - (* Star 0 *)
    exists []. split.
    + reflexivity. 
    + intros s' H. inversion H.
  - (* Star  *)
    destruct (IH2 Heqre') as [ss' [L R]].
    exists (s1::ss'). split.
    + simpl. rewrite <- L. reflexivity.
    + intros s' H. destruct H.
      { rewrite <- H. inversion Heqre'. rewrite H1 in Hmatch1. apply Hmatch1. }
      { apply R. apply H. }
Qed.

(** [] *)

(* ############################################################ *)

(** **** Exercise: 5 stars, advanced (pumping)  *)

Module Pumping.

(** One of the first interesting theorems in the theory of regular
    expressions is the so-called _pumping lemma_, which states,
    informally, that any sufficiently long string [s] matching a
    regular expression [re] can be "pumped" by repeating some middle
    section of [s] an arbitrary number of times to produce a new
    string also matching [re]. *)

(** To begin, we need to define "sufficiently long."  Since we are
    working in a constructive logic, we actually need to be able to
    calculate, for each regular expression [re], the minimum length
    for strings [s] to guarantee "pumpability." *)

Fixpoint pumping_constant {T} (re : reg_exp T) : nat :=
  match re with
  | EmptySet => 0
  | EmptyStr => 1
  | Char _ => 2
  | App re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Union re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Star _ => 1
  end.

(** Next, it is useful to define an auxiliary function that repeats a
    string (appends it to itself) some number of times. *)

Fixpoint napp {T} (n : nat) (l : list T) : list T :=
  match n with
  | 0 => []
  | S n' => l ++ napp n' l
  end.

Lemma napp_plus: forall T (n m : nat) (l : list T),
  napp (n + m) l = napp n l ++ napp m l.
Proof.
  intros T n m l.
  induction n as [|n IHn].
  - reflexivity.
  - simpl. rewrite IHn, app_assoc. reflexivity.
Qed.

(** Now, the pumping lemma itself says that, if [s =~ re] and if the
    length of [s] is at least the pumping constant of [re], then [s]
    can be split into three substrings [s1 ++ s2 ++ s3] in such a way
    that [s2] can be repeated any number of times and the result, when
    combined with [s1] and [s3] will still match [re].  Since [s2] is
    also guaranteed not to be the empty string, this gives us
    a (constructive!) way to generate strings matching [re] that are
    as long as we like. *)

Lemma pumping : forall T (re : reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.

(** To streamline the proof (which you are to fill in), the [omega]
    tactic, which is enabled by the following [Require], is helpful in
    several places for automatically completing tedious low-level
    arguments involving equalities or inequalities over natural
    numbers.  We'll return to [omega] in a later chapter, but feel
    free to experiment with it now if you like.  The first case of the
    induction gives an example of how it is used. *)

Require Import Coq.omega.Omega.

Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - (* MEmpty *)
    simpl. omega.
  - (* Char *)
    simpl. omega.
  - (* App *)
    simpl. 



Abort.




End Pumping.

(** [] *)

(* ####################################################### *)
(** * Improving Reflection *)

Theorem filter_not_empty_In : forall n l,
  filter (beq_nat n) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l = [] *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (beq_nat n m) eqn:H.
    + (* beq_nat n m = true *)
      intros _. rewrite beq_nat_true_iff in H. rewrite H.
      left. reflexivity.
    + (* beq_nat n m = false *)
      intros H'. right. apply IHl'. apply H'.
Qed.

Inductive reflect (P : Prop) : bool -> Prop :=
| ReflectT : P -> reflect P true
| ReflectF : ~ P -> reflect P false.


Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  intros P [] H.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. inversion H'.
Qed.

(** **** Exercise: 2 stars, recommended (reflect_iff)  *)
Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  intros P b R.
  destruct R as [ HP | NP ]. 
  - split; trivial.
  - split. 
    + intros HP. elim (NP HP).
    + intros H. inversion H.
Qed.

(** [] *)

Lemma beq_natP : forall n m, reflect (n = m) (beq_nat n m).
Proof.
  intros n m.
  apply iff_reflect. rewrite beq_nat_true_iff. reflexivity.
Qed.

Theorem filter_not_empty_In' : forall n l,
  filter (beq_nat n) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l = [] *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (beq_natP n m) as [H | H].
    + (* n = m *)
      intros _. rewrite H. left. reflexivity.
    + (* n <> m *)
      intros H'. right. apply IHl'. apply H'.
Qed.

(* ####################################################### *)
(** * Additional Exercises *)

(** **** Exercise: 4 stars, recommended (palindromes)  *)
(** A palindrome is a sequence that reads the same backwards as
    forwards.

    - Define an inductive proposition [pal] on [list X] that
      captures what it means to be a palindrome. (Hint: You'll need
      three cases.  Your definition should be based on the structure
      of the list; just having a single constructor
        c : forall l, l = rev l -> pal l
      may seem obvious, but will not work very well.)

    - Prove [pal_app_rev] that
       forall l, pal (l ++ rev l).
    - Prove [pal_rev] that
       forall l, pal l -> l = rev l.
*)

Inductive pal {X : Type} : list X -> Prop :=
  | Empty : pal []
  | Single : forall c, pal [c]
  | Sym : forall c l, pal l -> pal ([c]++ l ++ [c]).

Theorem pal_app_revl : forall (X:Type) (l:list X), pal (l ++ rev l).
Proof.
  intros X l.
  induction l as [|h t].
  - (* l = [] *)
    simpl. apply Empty.
  - (* l = h::t *)
    simpl. 
    assert (H: forall (T:Type) (x:T) l1, [x]++l1 = x::l1).
    { intros T x l1. simpl. reflexivity.  }
    rewrite <- H. rewrite app_assoc with (l:=t).
    apply Sym. apply IHt.
Qed.

Theorem pal_rev : forall (X:Type) (l:list X), pal l -> l = rev l.
Proof.
  intros X l P.
  induction P as [ | h IHh | h t P' IHh ].
  - (* Empty *)
    trivial.
  - (* Single *)
    trivial.
  - (* Sym *)
    simpl. rewrite rev_app_distr. simpl.
    rewrite <- IHh. reflexivity.
Qed.

(** [] *)

(** **** Exercise: 5 stars, optional (palindrome_converse)  *)
(** Again, the converse direction is significantly more difficult, due
    to the lack of evidence.  Using your definition of [pal] from the
    previous exercise, prove that
     forall l, l = rev l -> pal l.
*)

Theorem rev_pal : forall (X:Type) (l:list X), l = rev l -> pal l.
Proof.
  intros X l R.
  induction l as [|h t].
  - (* l = [] *)
    apply Empty.
  - (* l = h::t *)
    simpl in R.
    induction t as [|h' t'].
    + (* t = [] *)
      apply Single.
    + (* t = h'::t' *)
      simpl in R. 
Abort.

(** [] *)

(** **** Exercise: 4 stars, advanced (filter_challenge)  *)
(** Let's prove that our definition of [filter] from the [Poly]
    chapter matches an abstract specification.  Here is the
    specification, written out informally in English:

    A list [l] is an "in-order merge" of [l1] and [l2] if it contains
    all the same elements as [l1] and [l2], in the same order as [l1]
    and [l2], but possibly interleaved.  For example,
    [1;4;6;2;3]
    is an in-order merge of
    [1;6;2]
    and
    [4;3].
    Now, suppose we have a set [X], a function [test: X->bool], and a
    list [l] of type [list X].  Suppose further that [l] is an
    in-order merge of two lists, [l1] and [l2], such that every item
    in [l1] satisfies [test] and no item in [l2] satisfies test.  Then
    [filter test l = l1].

    Translate this specification into a Coq theorem and prove
    it.  (You'll need to begin by defining what it means for one list
    to be a merge of two others.  Do this with an inductive relation,
    not a [Fixpoint].)  *)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 5 stars, advanced, optional (filter_challenge_2)  *)
(** A different way to characterize the behavior of [filter] goes like
    this: Among all subsequences of [l] with the property that [test]
    evaluates to [true] on all their members, [filter test l] is the
    longest.  Formalize this claim and prove it. *)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 4 stars, advanced (NoDup)  *)
(** Recall the definition of the [In] property from the [Logic]
    chapter, which asserts that a value [x] appears at least once in a
    list [l]: *)

(* Fixpoint In (A : Type) (x : A) (l : list A) : Prop :=
   match l with
   | [] => False
   | x' :: l' => x' = x \/ In A x l'
   end *)

(** Your first task is to use [In] to define a proposition [disjoint X
    l1 l2], which should be provable exactly when [l1] and [l2] are
    lists (with elements of type X) that have no elements in
    common. *)

(* FILL IN HERE *)

(** Next, use [In] to define an inductive proposition [NoDup X
    l], which should be provable exactly when [l] is a list (with
    elements of type [X]) where every member is different from every
    other.  For example, [NoDup nat [1;2;3;4]] and [NoDup
    bool []] should be provable, while [NoDup nat [1;2;1]] and
    [NoDup bool [true;true]] should not be.  *)

(* FILL IN HERE *)

(** Finally, state and prove one or more interesting theorems relating
    [disjoint], [NoDup] and [++] (list append).  *)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 3 stars, recommended (nostutter)  *)
(** Formulating inductive definitions of properties is an important
    skill you'll need in this course.  Try to solve this exercise
    without any help at all.

    We say that a list "stutters" if it repeats the same element
    consecutively.  The property "[nostutter mylist]" means that
    [mylist] does not stutter.  Formulate an inductive definition for
    [nostutter].  (This is different from the [NoDup] property in the
    exercise above; the sequence [1;4;1] repeats but does not
    stutter.) *)

Inductive nostutter {X:Type} : list X -> Prop :=
 (* FILL IN HERE *)
.

(** Make sure each of these tests succeeds, but feel free to change
    the suggested proof (in comments) if the given one doesn't work
    for you.  Your definition might be different from ours and still
    be correct, in which case the examples might need a different
    proof.  (You'll notice that the suggested proofs use a number of
    tactics we haven't talked about, to make them more robust to
    different possible ways of defining [nostutter].  You can probably
    just uncomment and use them as-is, but you can also prove each
    example with more basic tactics.)  *)

Example test_nostutter_1: nostutter [3;1;4;1;5;6].
(* FILL IN HERE *) Admitted.
(* 
  Proof. repeat constructor; apply beq_nat_false_iff; auto.
  Qed.
*)

Example test_nostutter_2:  nostutter (@nil nat).
(* FILL IN HERE *) Admitted.
(* 
  Proof. repeat constructor; apply beq_nat_false_iff; auto.
  Qed.
*)

Example test_nostutter_3:  nostutter [5].
(* FILL IN HERE *) Admitted.
(* 
  Proof. repeat constructor; apply beq_nat_false; auto. Qed.
*)

Example test_nostutter_4:      not (nostutter [3;1;1;4]).
(* FILL IN HERE *) Admitted.
(* 
  Proof. intro.
  repeat match goal with
    h: nostutter _ |- _ => inversion h; clear h; subst
  end.
  contradiction H1; auto. Qed.
*)
(** [] *)

(** **** Exercise: 4 stars, advanced (pigeonhole principle)  *)
(** The _pigeonhole principle_ states a basic fact about counting: if
   we distribute more than [n] items into [n] pigeonholes, some
   pigeonhole must contain at least two items.  As often happens, this
   apparently trivial fact about numbers requires non-trivial
   machinery to prove, but we now have enough... *)

(** First prove an easy useful lemma. *)

Lemma in_split : forall (X:Type) (x:X) (l:list X),
  In x l ->
  exists l1 l2, l = l1 ++ x :: l2.
Proof.
  (* FILL IN HERE *) Admitted.

(** Now define a property [repeats] such that [repeats X l] asserts
    that [l] contains at least one repeated element (of type [X]).  *)

Inductive repeats {X:Type} : list X -> Prop :=
  (* FILL IN HERE *)
.

(** Now, here's a way to formalize the pigeonhole principle.  Suppose
    list [l2] represents a list of pigeonhole labels, and list [l1]
    represents the labels assigned to a list of items.  If there are
    more items than labels, at least two items must have the same
    label -- i.e., list [l1] must contain repeats.

    This proof is much easier if you use the [excluded_middle]
    hypothesis to show that [In] is decidable, i.e. [forall x l, (In x
    l) \/ ~ (In x l)].  However, it is also possible to make the proof
    go through _without_ assuming that [In] is decidable; if you
    manage to do this, you will not need the [excluded_middle]
    hypothesis. *)

Theorem pigeonhole_principle: forall (X:Type) (l1  l2:list X),
   excluded_middle ->
   (forall x, In x l1 -> In x l2) ->
   length l2 < length l1 ->
   repeats l1.
Proof.
   intros X l1. induction l1 as [|x l1' IHl1'].
  (* FILL IN HERE *) Admitted.
(** [] *)



(** $Date: 2015-08-11 12:03:04 -0400 (Tue, 11 Aug 2015) $ *)
