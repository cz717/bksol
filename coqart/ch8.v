


(* Exercise 8.5 *)

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


(* Exercise 8.6 *)

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



(* Exercise 8.7 *)

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

