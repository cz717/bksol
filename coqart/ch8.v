

(** ** Chapter 8. Inductive Predicates *)

Require Import List.
Import ListNotations.

Require Import Relations.
Require Import Le.
Require Import ch5.

(** **** Exercise 8.1 *)

Inductive last (A : Set) : A -> list A -> Prop :=
| last1 : forall a:A, last A a (a::nil)
| last2 : forall (a x : A) (l : list A), last A a l -> last A a (x::l).

Fixpoint last_fun (A : Set) (l : list A) : option A :=
  match l with
    | [] => None
    | [a] => Some a
    | h::t => last_fun A t
  end.

Theorem lasteq : forall (A : Set) (a : A) (l : list A),
  last A a l <-> last_fun A l = Some a.
Proof.
  intros A a l.
  generalize dependent a.
  induction l as [|h t].
  - split; intros H; inversion H.
  - split; intros H. 
    + simpl. destruct t as [|h' t'].
      * inversion H. reflexivity.
        inversion H2.
      * apply IHt. inversion H. assumption.
    + simpl in H. destruct t as [|h' t'].
      * injection H. intros E. rewrite E. apply last1.
      * apply last2. rewrite IHt. assumption.
Qed.

(** [] *)


(** **** Exercise 8.2 *)

Inductive palindrome (A : Set) : list A -> Prop :=
| pal0 : palindrome A []
| pal1 : forall x : A, palindrome A [x]
| pal2 : forall (x : A) (l : list A), palindrome A l -> palindrome A ([x]++l++[x]).

(** [] *)


(** **** Exercise 8.3 *)
(** [] *)


(** **** Exercise 8.4 *)

Inductive tsp (A : Set) : relation (list A) :=
| tsp1 : forall (a b : A) (l : list A), tsp A (a::b::l) (b::a::l)
| tsp2 : forall (x : A) (l1 l2 : list A), tsp A l1 l2 -> tsp A (x::l1) (x::l2).

Inductive pmt (A : Set) : relation (list A) :=
| pmt1 : forall (l1 l2 : list A), tsp A l1 l2 -> pmt A l1 l2
| pmt2 : forall (l1 l2 l3 : list A), pmt A l1 l2 -> tsp A l2 l3 -> pmt A l1 l3.

(** proof...  *)

(** [] *)


(** **** Exercise 8.5 *)

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





(** **** Exercise 8.12 *)

Theorem le_my_le : forall n p : nat, n <= p -> my_le n p.
Proof.
  unfold my_le. intros n p np P Pn H.
  elim np; trivial.
  intros m nm Pm. apply H. assumption.
Qed.  

(** [] *)



(** **** Exercise 8.13 *)

Theorem le_trans' : forall n p q : nat, n <= p -> p <= q -> n <= q.
Proof.
  intros n p q np pq.
  induction np as [|m nm IH]; trivial.
  apply IH. apply le_Sn_le. assumption.
Qed.

Theorem my_le_trans : forall n p q : nat, my_le n p -> my_le p q -> my_le n q.
Proof.
  unfold my_le. intros n p q np pq.
  intros P Pn H.
  apply pq; try assumption.
  apply np; try assumption.
Qed.

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


(** **** Exercise 8.15 *)

Inductive sorted (A : Set) (R : relation A) : list A -> Prop :=
| sorted0 : sorted A R []
| sorted1 : forall x : A, sorted A R [x]
| sorted2 : forall (x y : A) (l : list A), 
              R x y -> sorted A R (y::l) -> sorted A R (x::y::l).

Definition sorted' (A : Set) (R : relation A) (l : list A) :=
  forall (l1 l2 : list A) (n1 n2 : A),
    l = l1 ++ (n1::n2::l2) -> R n1 n2.

Theorem sorted_eq : forall (A : Set) (R : relation A) (l : list A),
  sorted A R l <-> sorted' A R l.
Proof.
  intros A R l. split; intros H.
  - (* -> *)
    unfold sorted'.
    induction H; intros l1 l2 n1 n2 H'.
    + destruct l1; simpl in H'; discriminate H'.
    + repeat (destruct l1; simpl in H'; try discriminate H').
    + destruct l1 as [|h t].
      * simpl in H'. injection H'.
        intros H1 H2 H3. rewrite <- H2. rewrite <- H3. assumption.
      * simpl in H'. injection H'.
        intros H1 H2. apply (IHsorted t l2). assumption.
  - (* <- *)
    unfold sorted' in H.
    induction l as [|h t]; try (constructor; fail).
    destruct t as [|h' t']; try (constructor; fail).
    apply sorted2.
    + apply (H [] t'). reflexivity.
    + apply IHt. intros l1 l2 n1 n2 H'.
      apply (H (h::l1) l2). simpl.
      rewrite H'. reflexivity.
Qed.
        

(** [] *)


(** **** Exercise 8.18 *)

Section weird_induc_proof.

Variable P : nat -> Prop.
Variable f : nat -> nat.

Hypothesis f_strict_mono : forall n p : nat, lt n p -> lt (f n) (f p).
Hypothesis f_0 : lt 0 (f 0).

Hypothesis P0 : P 0.
Hypothesis P_Sn_n : forall n : nat, P (S n) -> P n.
Hypothesis f_P : forall n : nat, P n -> P (f n).

Lemma nltfn : forall n : nat, lt n (f n).
Proof.
  induction n as [|n'].
  - assumption.
  - unfold lt. unfold lt in IHn'.
    apply le_trans with (m:= S (f n')).
    + apply le_n_S. assumption.
    + apply f_strict_mono. unfold lt. apply le_n.
Qed.

Lemma P_le : forall n m, n <= m -> P m -> P n.
Proof.
  intros n m nm Pm.
  induction nm; trivial.
  apply IHnm. apply P_Sn_n. assumption.
Qed.

Theorem weird_induc : forall n : nat, P n.
Proof.
  induction n as [|n'].
  - assumption.
  - apply (P_le _ (f n')).
    + apply nltfn.
    + apply f_P. assumption.
Qed.

End weird_induc_proof.

(** [] *)


(** **** Exercise 8.24 *)

Inductive parse_rel : list par -> list par -> bin -> Prop :=
  | parse_node : 
      forall (l1 l2 l3 : list par) (t1 t2 : bin),
        parse_rel l1 (close::l2) t1 -> parse_rel l2 l3 t2 ->
        parse_rel (open::l1) l3 (N t1 t2)
  | parse_leaf_nil :
      parse_rel [] [] L
  | parse_leaf_close :
      forall l : list par, parse_rel (close::l) (close::l) L.

Lemma parse_rel_sound_aux :
  forall (l1 l2 : list par) (t : bin),
    parse_rel l1 l2 t -> l1 = (bin_to_string t) ++ l2.
Proof.
  intros l1 l2 t H.
  induction H.
  - simpl. rewrite IHparse_rel1. rewrite IHparse_rel2.
    rewrite <- app_assoc. simpl. reflexivity.
  - trivial.
  - trivial.
Qed.

Lemma parse_rel_sound :
  forall l : list par, (exists t : bin, parse_rel l nil t) -> wp l.
Proof.
  intros l [t H].
  rewrite (parse_rel_sound_aux l [] t H).
  rewrite app_nil_r. apply wp_btos.
Qed.

(** [] *)


Section little_semantics.

Variables Var aExp bExp : Set.

Inductive inst : Set :=
| Skip : inst
| Assign : Var -> aExp -> inst
| Sequence : inst -> inst -> inst
| WhileDo : bExp -> inst -> inst.

Require Import ZArith.

Variables 
(state : Set)
(update : state -> Var -> Z -> option state)
(evalA : state -> aExp -> option Z)
(evalB : state -> bExp -> option bool).



(** **** Exercise 8.5 *)
(** [] *)


(** **** Exercise 8.5 *)
(** [] *)


(** **** Exercise 8.5 *)
(** [] *)


(** **** Exercise 8.5 *)
(** [] *)


(** **** Exercise 8.5 *)
(** [] *)


(** **** Exercise 8.5 *)
(** [] *)
