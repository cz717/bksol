(** * Induction: Proof by Induction *)

Require Export Basics.

(* ###################################################################### *)
(** * Naming Cases *)

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

Theorem andb_true_elim1 : forall b c : bool,
  andb b c = true -> b = true.
Proof.
  intros b c H.
  destruct b.
  Case "b = true".  (* <----- here *)
    reflexivity.
  Case "b = false".  (* <---- and here *)
    rewrite <- H. 
    reflexivity.  
Qed.



(** **** Exercise: 2 stars (andb_true_elim2)  *)
(** Prove [andb_true_elim2], marking cases (and subcases) when
    you use [destruct]. *)

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c. intros H.
  destruct c.
  Case "c = true".
    reflexivity.
  Case "c = false".
    simpl in H.
    rewrite <- H.
    destruct b.
      reflexivity.
      reflexivity.
Qed.
    
(** [] *)




(* ###################################################################### *)
(** * Proof by Induction *)

Theorem plus_0_r_firsttry : forall n:nat,
  n + 0 = n.
Proof.
  intros n.
  simpl. (* Does nothing! *)
Abort.

(** *** *)

Theorem plus_0_r_secondtry : forall n:nat,
  n + 0 = n.
Proof.
  intros n. destruct n as [| n'].
  Case "n = 0".
    reflexivity. (* so far so good... *)
  Case "n = S n'".
    simpl.       (* ...but here we are stuck again *)
Abort.

(** *** *)

(** *** *)

Theorem plus_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".     reflexivity.
  Case "n = S n'".  simpl. rewrite -> IHn'. reflexivity.  
Qed.


Theorem minus_diag : forall n,
  minus n n = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n. induction n as [| n'].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity.  
Qed.



(** **** Exercise: 2 stars (basic_induction)  *)

(** Prove the following lemmas using induction. You might need
    previously proven results. *)

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n.
  induction n as [|n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl. rewrite IHn'. reflexivity.
Qed.



Theorem plus_n_Sm : forall n m : nat, 
  S (n + m) = n + (S m).
Proof. 
  intros n m.
  induction n as [|n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl. rewrite IHn'. reflexivity.
Qed.



Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n as [|n'].
  Case "n = 0".
    rewrite plus_0_r. reflexivity.
  Case "n = S n'".
    simpl. rewrite IHn'.
    rewrite plus_n_Sm. reflexivity.
Qed.


Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [|n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl. rewrite IHn'. reflexivity.
Qed.
(** [] *)




(** **** Exercise: 2 stars (double_plus)  *)

(** Consider the following function, which doubles its argument: *)

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

(** Use induction to prove this simple fact about [double]: *)

Lemma double_plus : forall n, double n = n + n .
Proof.  
  intros n.
  induction n as [|n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl. rewrite IHn'. rewrite plus_n_Sm. reflexivity.
Qed.
(** [] *)



(** **** Exercise: 1 star (destruct_induction)  *)
(** Briefly explain the difference between the tactics
    [destruct] and [induction].  

(* FILL IN HERE *)

*)
(** [] *)



(* ###################################################################### *)
(** * Proofs Within Proofs *)

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). 
    Case "Proof of assertion". reflexivity.
  rewrite -> H.
  reflexivity.  Qed.


Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  (* We just need to swap (n + m) for (m + n)...
     it seems like plus_comm should do the trick! *)
  rewrite -> plus_comm.
  (* Doesn't work...Coq rewrote the wrong plus! *)
Abort.


Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
    Case "Proof of assertion".
    rewrite -> plus_comm. reflexivity.
  rewrite -> H. reflexivity.  Qed.



(** **** Exercise: 4 stars (mult_comm)  *)
(** Use [assert] to help prove this theorem.  You shouldn't need to
    use induction. *)

Theorem plus_swap : forall n m p : nat, 
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite plus_assoc.
  rewrite plus_assoc.
  assert (H: n + m = m + n).
    Case "Proof of assertion".
    rewrite -> plus_comm. reflexivity.
  rewrite H. reflexivity.
Qed.


(** Now prove commutativity of multiplication.  (You will probably
    need to define and prove a separate subsidiary theorem to be used
    in the proof of this one.)  You may find that [plus_swap] comes in
    handy. *)

Theorem mult_comm : forall m n : nat,
 m * n = n * m.
Proof.
  intros m.
  induction m as [|m'].
  Case "m = 0".
    intros n. rewrite mult_0_r. reflexivity.
  Case "m = S m'".
    intros n. simpl.
    assert (H : n * S m' = n + n * m').
      induction n as [|n'].
      SCase "n = 0".
        reflexivity.
      SCase "n = S n'".
        simpl. rewrite IHn'.
        rewrite plus_swap. reflexivity.
    rewrite H. rewrite IHm'. reflexivity.
Qed.
      
(** [] *)



(** **** Exercise: 2 stars, optional (evenb_n__oddb_Sn)  *)

(** Prove the following simple fact: *)

Theorem evenb_n__oddb_Sn : forall n : nat,
  evenb n = negb (evenb (S n)).
Proof.
  intros n.
  induction n as [|n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    assert (evenb (S (S n')) = evenb n') as H.
      SCase "Proof of assertion". reflexivity.
    rewrite H. rewrite IHn'. rewrite negb_involutive. reflexivity.
Qed.
(** [] *)


(* ###################################################################### *)
(** * More Exercises *)

(** **** Exercise: 3 stars, optional (more_exercises)  *)
(** Take a piece of paper.  For each of the following theorems, first
    _think_ about whether (a) it can be proved using only
    simplification and rewriting, (b) it also requires case
    analysis ([destruct]), or (c) it also requires induction.  Write
    down your prediction.  Then fill in the proof.  (There is no need
    to turn in your piece of paper; this is just to encourage you to
    reflect before hacking!) *)

Theorem ble_nat_refl : forall n:nat,
  true = ble_nat n n.
Proof.
  intros n.
  induction n as [|n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl. rewrite IHn'. reflexivity.
Qed.

Theorem zero_nbeq_S : forall n:nat,
  beq_nat 0 (S n) = false.
Proof.
  intros n.
  reflexivity.
Qed.


Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  intros b.
  destruct b.
    reflexivity.
    reflexivity.
Qed.


Theorem plus_ble_compat_l : forall n m p : nat, 
  ble_nat n m = true -> ble_nat (p + n) (p + m) = true.
Proof.
  intros n m p. intros H.
  induction p as [|p'].
  Case "p = 0".
    simpl. apply H.
  Case "p = S p'".
    simpl. apply IHp'.
Qed.


Theorem S_nbeq_0 : forall n:nat,
  beq_nat (S n) 0 = false.
Proof.
  intros n. reflexivity.
Qed.


Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  intros n. simpl. rewrite plus_0_r. reflexivity.
Qed.


Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
Proof.
  destruct b.
    destruct c.
      reflexivity.
      reflexivity.
    destruct c.
      reflexivity.
      reflexivity.
Qed.


Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p.
  induction n as [|n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl. rewrite IHn'. rewrite plus_assoc. reflexivity.
Qed.


Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p.
  induction n as [|n'].
  Case "n = 0". 
    reflexivity.
  Case "n = S n'".
    simpl. rewrite 
    mult_plus_distr_r.
    rewrite IHn'. 
    reflexivity.
Qed.
(** [] *)

(** **** Exercise: 2 stars, optional (beq_nat_refl)  *)
(** Prove the following theorem.  Putting [true] on the left-hand side
of the equality may seem odd, but this is how the theorem is stated in
the standard library, so we follow suit.  Since rewriting 
works equally well in either direction, we will have no 
problem using the theorem no matter which way we state it. *)

Theorem beq_nat_refl : forall n : nat, 
  true = beq_nat n n.
Proof.
  intros n.
  induction n as [|n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl. rewrite IHn'. reflexivity.
Qed.



(** **** Exercise: 2 stars, optional (plus_swap')  *)
(** The [replace] tactic allows you to specify a particular subterm to
   rewrite and what you want it rewritten to.  More precisely,
   [replace (t) with (u)] replaces (all copies of) expression [t] in
   the goal by expression [u], and generates [t = u] as an additional
   subgoal. This is often useful when a plain [rewrite] acts on the wrong
   part of the goal.  

   Use the [replace] tactic to do a proof of [plus_swap'], just like
   [plus_swap] but without needing [assert (n + m = m + n)]. 
*)

Theorem plus_swap' : forall n m p : nat, 
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite plus_assoc.
  rewrite plus_assoc.
  replace (n + m) with (m + n). reflexivity.
  Case "Proof m+n = n+m".
    rewrite plus_comm. reflexivity.
Qed.
    


(** **** Exercise: 3 stars (binary_commute)  *)
(** Recall the [increment] and [binary-to-unary] functions that you
    wrote for the [binary] exercise in the [Basics] chapter.  Prove
    that these functions commute -- that is, incrementing a binary
    number and then converting it to unary yields the same result as
    first converting it to unary and then incrementing.
    Name your theorem [bin_to_nat_pres_incr].

    (Before you start working on this exercise, please copy the
    definitions from your solution to the [binary] exercise here so
    that this file can be graded on its own.  If you find yourself
    wanting to change your original definitions to make the property
    easier to prove, feel free to do so.) *)

Inductive bin : Type :=
  | Z : bin
  | T : bin -> bin
  | ST : bin -> bin.

Fixpoint incr (b : bin): bin :=
  match b with
    | Z => ST Z
    | T b' => ST b'
    | ST b' => T (incr b')
  end.

Fixpoint bin_to_nat (b : bin): nat :=
  match b with
    | Z => O
    | T b' => double (bin_to_nat b')
    | ST b' => S (double (bin_to_nat b'))
  end.


Theorem bin_comm : forall b : bin,
  bin_to_nat (incr b) = S (bin_to_nat b).
Proof.
  intros b.
  induction b as [|b'|b'].
  Case "b = Z".
    reflexivity.
  Case "b = T b'".
    reflexivity.
  Case "b = ST b'".
    simpl. rewrite IHb'. reflexivity.
Qed.

(* FILL IN HERE *)
(** [] *)


(** **** Exercise: 5 stars, advanced (binary_inverse)  *)
(** This exercise is a continuation of the previous exercise about
    binary numbers.  You will need your definitions and theorems from
    the previous exercise to complete this one.

    (a) First, write a function to convert natural numbers to binary
        numbers.  Then prove that starting with any natural number,
        converting to binary, then converting back yields the same
        natural number you started with.

    (b) You might naturally think that we should also prove the
        opposite direction: that starting with a binary number,
        converting to a natural, and then back to binary yields the
        same number we started with.  However, it is not true!
        Explain what the problem is.

    (c) Define a "direct" normalization function -- i.e., a function
        [normalize] from binary numbers to binary numbers such that,
        for any binary number b, converting to a natural and then back
        to binary yields [(normalize b)].  Prove it.  (Warning: This
        part is tricky!)

    Again, feel free to change your earlier definitions if this helps
    here. 
*)

(** (a): *)
Fixpoint nat_to_bin (n : nat) :=
  match n with
    | O => Z
    | S n' => incr (nat_to_bin n')
  end.

Theorem nat_bin_nat : forall n : nat,
  bin_to_nat (nat_to_bin n) = n.
proof.
  intros n.
  induction n as [|n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite bin_comm.
    rewrite IHn'.
    reflexivity.
Qed.

(** (b): *)
(** for bin Z, (T Z), (T (T Z),..., and so on, are all correspond to
    nat O. So (nat_to_bin (bin_to_nat (T Z))) = Z, but not (T Z).
*)

(** (c): *)
Definition bin_normal (b : bin) : bin :=
  nat_to_bin (bin_to_nat b).


(* FILL IN HERE *)
(** [] *)



(* ###################################################################### *)
(** * Formal vs. Informal Proof (Advanced) *)

Theorem plus_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. intros n m p. induction n as [| n']. reflexivity. 
  simpl. rewrite -> IHn'. reflexivity.  Qed.


Theorem plus_assoc'' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n']. 
  Case "n = 0".
    reflexivity. 
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity.   Qed.



(** **** Exercise: 2 stars, advanced (plus_comm_informal)  *)
(** Translate your solution for [plus_comm] into an informal proof. *)

(** Theorem: Addition is commutative.
 
    Proof: (* FILL IN HERE *)
*)
(** [] *)



(** **** Exercise: 2 stars, optional (beq_nat_refl_informal)  *)
(** Write an informal proof of the following theorem, using the
    informal proof of [plus_assoc] as a model.  Don't just
    paraphrase the Coq tactics into English!
 
    Theorem: [true = beq_nat n n] for any [n].
    
    Proof: (* FILL IN HERE *) 
[] *)

(** $Date: 2014-12-31 15:31:47 -0500 (Wed, 31 Dec 2014) $ *)
