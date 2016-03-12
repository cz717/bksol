(** * IndPrinciples: Induction Principles *)

Require Export ProofObjects.

(* ##################################################### *)
(** * Basics *)

Check nat_ind.

Theorem mult_0_r' : forall n:nat,
  n * 0 = 0.
Proof.
  apply nat_ind.
  - (* n = O *) reflexivity.
  - (* n = S n' *) simpl. intros n' IHn'. rewrite -> IHn'.
    reflexivity.  Qed.


(** **** Exercise: 2 stars, optional (plus_one_r')  *)
(** Complete this proof without using the [induction] tactic. *)

Theorem plus_one_r' : forall n:nat,
  n + 1 = S n.
Proof.
  apply nat_ind.
  - reflexivity.
  - simpl. intros n IH.
    rewrite IH. reflexivity.
Qed.

(** [] *)

Inductive yesno : Type :=
  | yes : yesno
  | no : yesno.

Check yesno_ind.


(** **** Exercise: 1 star, optional (rgb)  *)
(** Write out the induction principle that Coq will generate for the
    following datatype.  Write down your answer on paper or type it
    into a comment, and then compare it with what Coq prints. *)

Inductive rgb : Type :=
  | red : rgb
  | green : rgb
  | blue : rgb.
Check rgb_ind.
(** [] *)

Inductive natlist : Type :=
  | nnil : natlist
  | ncons : nat -> natlist -> natlist.

Check natlist_ind.

(** **** Exercise: 1 star, optional (natlist1)  *)

Inductive natlist1 : Type :=
  | nnil1 : natlist1
  | nsnoc1 : natlist1 -> nat -> natlist1.

(** Now what will the induction principle look like? *)
(** [] *)

(** **** Exercise: 1 star, optional (byntree_ind)  *)
(** Write out the induction principle that Coq will generate for the
    following datatype.  (Again, write down your answer on paper or
    type it into a comment, and then compare it with what Coq
    prints.) *)

Inductive byntree : Type :=
 | bempty : byntree
 | bleaf  : yesno -> byntree
 | nbranch : yesno -> byntree -> byntree -> byntree.
(** [] *)


(** **** Exercise: 1 star, optional (ex_set)  *)
(** Here is an induction principle for an inductively defined
    set.
      ExSet_ind :
         forall P : ExSet -> Prop,
             (forall b : bool, P (con1 b)) ->
             (forall (n : nat) (e : ExSet), P e -> P (con2 n e)) ->
             forall e : ExSet, P e
    Give an [Inductive] definition of [ExSet]: *)

Inductive ExSet : Type :=
  | con1 : bool -> ExSet
  | con2 : nat -> ExSet -> ExSet.

(** [] *)

(** * Polymorphism *)

(** **** Exercise: 1 star, optional (tree)  *)
(** Write out the induction principle that Coq will generate for
   the following datatype.  Compare your answer with what Coq
   prints. *)

Inductive tree (X:Type) : Type :=
  | leaf : X -> tree X
  | node : tree X -> tree X -> tree X.
Check tree_ind.
(** [] *)

(** **** Exercise: 1 star, optional (mytype)  *)
(** Find an inductive definition that gives rise to the
    following induction principle:
      mytype_ind :
        forall (X : Type) (P : mytype X -> Prop),
            (forall x : X, P (constr1 X x)) ->
            (forall n : nat, P (constr2 X n)) ->
            (forall m : mytype X, P m ->
               forall n : nat, P (constr3 X m n)) ->
            forall m : mytype X, P m
*) 

Inductive mytype (X : Type) : Type := 
  | constr1 : X -> mytype X 
  | constr2 : nat -> mytype X 
  | constr3 : mytype X -> nat -> mytype X.

(** [] *)

(** **** Exercise: 1 star, optional (foo)  *)
(** Find an inductive definition that gives rise to the
    following induction principle:
      foo_ind :
        forall (X Y : Type) (P : foo X Y -> Prop),
             (forall x : X, P (bar X Y x)) ->
             (forall y : Y, P (baz X Y y)) ->
             (forall f1 : nat -> foo X Y,
               (forall n : nat, P (f1 n)) -> P (quux X Y f1)) ->
             forall f2 : foo X Y, P f2
*) 

Inductive foo (X Y : Type) : Type :=
  | bar : X -> foo X Y
  | baz : Y -> foo X Y
  | quux : (nat -> foo X Y) -> nat -> foo X Y.

(** [] *)

(** **** Exercise: 1 star, optional (foo')  *)
(** Consider the following inductive definition: *)

Inductive foo' (X:Type) : Type :=
  | C1 : list X -> foo' X -> foo' X
  | C2 : foo' X.

(** What induction principle will Coq generate for [foo']?  Fill
   in the blanks, then check your answer with Coq.)
     foo'_ind :
        forall (X : Type) (P : foo' X -> Prop),
              (forall (l : list X) (f : foo' X),
                    _______________________ ->
                    _______________________   ) ->
             ___________________________________________ ->
             forall f : foo' X, ________________________
*)

(** [] *)

(* ##################################################### *)
(** * Induction Hypotheses *)

Definition P_m0r (n:nat) : Prop :=
  n * 0 = 0.

Definition P_m0r' : nat->Prop :=
  fun n => n * 0 = 0.

Theorem mult_0_r'' : forall n:nat,
  P_m0r n.
Proof.
  apply nat_ind.
  - (* n = O *) reflexivity.
  - (* n = S n' *)
    (* Note the proof state at this point! *)
    intros n IHn.
    unfold P_m0r in IHn. unfold P_m0r. simpl. apply IHn. Qed.

(* ##################################################### *)
(** * More on the [induction] Tactic *)

Theorem plus_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| n'].
  - (* n = O *) reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity.  Qed.

Theorem plus_comm' : forall n m : nat,
  n + m = m + n.
Proof.
  induction n as [| n'].
  - (* n = O *) intros m. rewrite <- plus_n_O. reflexivity.
  - (* n = S n' *) intros m. simpl. rewrite -> IHn'.
    rewrite <- plus_n_Sm. reflexivity.  Qed.

Theorem plus_comm'' : forall n m : nat,
  n + m = m + n.
Proof.
  (* Let's do induction on [m] this time, instead of [n]... *)
  induction m as [| m'].
  - (* m = O *) simpl. rewrite <- plus_n_O. reflexivity.
  - (* m = S m' *) simpl. rewrite <- IHm'.
    rewrite <- plus_n_Sm. reflexivity.  Qed.

(** **** Exercise: 1 star, optional (plus_explicit_prop)  *)
(** Rewrite both [plus_assoc'] and [plus_comm'] and their proofs in
    the same style as [mult_0_r''] above -- that is, for each theorem,
    give an explicit [Definition] of the proposition being proved by
    induction, and state the theorem and proof in terms of this
    defined proposition.  *)

(* FILL IN HERE *)
(** [] *)


(* ##################################################### *)
(** * Induction Principles in [Prop] *)

Check ev_ind.

Theorem ev_ev' : forall n, ev n -> ev' n.
Proof.
  apply ev_ind.
  - (* ev_0 *)
    apply ev'_0.
  - (* ev_SS *)
    intros m Hm IH.
    apply (ev'_sum 2 m).
    + apply ev'_2.
    + apply IH.
Qed.

Inductive le (n:nat) : nat -> Prop :=
  | le_n : le n n
  | le_S : forall m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).

Check le_ind.

(* ####################################################### *)
(** * Formal vs. Informal Proofs by Induction *)

(** ** Induction Over an Inductively Defined Set *)

(** ** Induction Over an Inductively Defined Proposition *)

(** $Date: 2016-02-17 17:39:13 -0500 (Wed, 17 Feb 2016) $ *)
