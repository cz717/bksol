



(** **** Exercise 8.5 *)

Require Import List.
Import ListNotations.


Inductive par: Set := open | close.

Inductive wp : list par -> Prop :=
  | wpnil : wp nil
  | wpbt  : forall l, wp l -> wp ([open]++l++[close])
  | wpcat : forall l1 l2, wp l1 -> wp l2 -> wp (l1++l2).


Theorem wp_oc : wp (cons open (cons close nil)).
Proof.
  apply (wpbt []).
  apply wpnil.
Qed.

Theorem wp_o_head_c : forall  l1 l2: list par,
  wp l1 -> wp l2 -> wp (cons open (app l1 (cons close l2))).
Proof.
  intros l1 l2 H1 H2.
  cut (wp (([open] ++ l1 ++ [close]) ++ l2)).
  - intros H. simpl in H.
    rewrite <- app_assoc in H. 
    simpl in H. apply H.
  - apply (wpcat ([open] ++ l1 ++ [close]) l2).
    + apply (wpbt l1). assumption.
    + assumption.
Qed.

Theorem wp_o_tail_c : forall l1 l2 : list par,
  wp l1 -> wp l2 -> wp (app l1 (cons open (app l2 (cons close nil)))).
Proof.
  intros l1 l2 H1 H2.
  cut (wp (l1 ++ ([open] ++ l2 ++ [close]))).
  - intro H. simpl in H. assumption.
  - apply wpcat.
    + assumption.
    + apply wpbt; assumption.
Qed.

(** [] *)


(** **** Exercise 8.6 *)

Inductive bin : Set :=
  | L : bin
  | N : bin -> bin -> bin.

Fixpoint bin_to_string (t:bin) : list par :=
  match t with
    | L => nil
    | N u v => cons open (app (bin_to_string u) (cons close (bin_to_string v)))
  end.


Theorem wp_btos : forall t:bin, wp (bin_to_string t).
Proof.
  intros t.
  induction t as [|l IHL r IHR] ; simpl.
  - apply wpnil.
  - cut (wp (([open] ++ bin_to_string l ++ [close]) ++ bin_to_string r)).
    + intro H. simpl in H.
      rewrite <- app_assoc in H. simpl in H. apply H.
    + apply wpcat.
      * apply wpbt; assumption.
      * assumption.
Qed.

(** [] *)


(** **** Exercise 8.7 *)

Fixpoint bin_to_string' (t:bin) : list  par :=
  match t with
    | L => nil
    | N u v => app (bin_to_string' u)
                   (cons open (app (bin_to_string' v) (cons close nil)))
  end.


Theorem wp_btos' : forall t:bin, wp (bin_to_string' t).
Proof.
  intros t.
  induction t as [|l IHL r IHR] ; simpl.
  - apply wpnil.
  - apply wpcat.
    + assumption.
    + cut (wp ([open] ++ bin_to_string' r ++ [close])).
      * intros H. simpl in H. assumption.
      * apply wpbt. assumption.
Qed.

(** [] *)




(** * 8.3 Reasoning about Inductive Properties *)


(** **** Exercise 8.11 *)

Theorem lt_le : forall n p : nat, n < p -> n <= p.
Proof.
  intros n p H. unfold lt in H.
Admitted.

(** [] *)



(** **** Exercise 8.14 *)

Inductive le_diff (n m : nat) : Prop :=
  le_d : forall x:nat, x + n = m -> le_diff n m.


Theorem le_eq_deff : forall n m : nat, 
  n <= m <-> le_diff n m.
Proof.
  intros n m. split.
  - (* -> *)
    intros H. elim H.
    + apply (le_d n n 0). trivial.
    + intros m' H' IH. 
      destruct IH as [x' P].
      apply (le_d n (S m') (S x')).
      simpl. rewrite P. reflexivity.
  - (* <- *)
    intros [x P]. 
    generalize dependent m.
    generalize dependent n.
    induction x as [|x'].
    + intros n m H. simpl in H. rewrite H. apply le_n.
    + intros n m H. simpl in H.
      rewrite <- H. apply le_S.
      apply IHx'. reflexivity.
Qed.

(** [] *)


(** **** Exercise 8.15 *)

Inductive le' : nat -> nat -> Prop :=
  | le'_O_p : forall p : nat, le' 0 p
  | le'_Sn_Sp : forall n p : nat, le' n p -> le' (S n) (S p).

Theorem le_eq_le' : forall n m : nat,
  le n m <-> le' n m.
Proof.
  split; intros H.
  - induction H.
    + elim n ; repeat constructor; assumption.
    + induction IHle.
      * constructor.
      * constructor. apply IHIHle.
        apply le_S_n. assumption.
  - induction H.
    + apply le_0_n.
    + apply le_n_S. assumption.
Qed.

(** [] *)
