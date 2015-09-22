(** * MoreInd: More on Induction *)

Require Export "ProofObjects".

(* ##################################################### *)
(** * Induction Principles *)

Check nat_ind.

Theorem mult_0_r' : forall n:nat, 
  n * 0 = 0.
Proof.
  apply nat_ind. 
  Case "O". reflexivity.
  Case "S". simpl. intros n IHn. rewrite -> IHn. 
    reflexivity.  Qed.



(** **** Exercise: 2 stars, optional (plus_one_r')  *)
(** Complete this proof as we did [mult_0_r'] above, without using
    the [induction] tactic. *)

Theorem plus_one_r' : forall n:nat, 
  n + 1 = S n.
Proof.
  apply nat_ind. 
  Case "O". reflexivity.
  Case "S". intros n IHn. simpl. rewrite IHn. reflexivity.
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
(* rgb_ind : forall P: rgb -> Prop,
               P red ->
               P green ->
               P blue ->
             forall r : rgb, P r *)
   
(** [] *)



Inductive natlist : Type :=
  | nnil : natlist
  | ncons : nat -> natlist -> natlist.

Check natlist_ind.



(** **** Exercise: 1 star, optional (natlist1)  *)
(** Suppose we had written the above definition a little
   differently: *)

Inductive natlist1 : Type :=
  | nnil1 : natlist1
  | nsnoc1 : natlist1 -> nat -> natlist1.

(** Now what will the induction principle look like? *)
(* natlist1_ind : forall P : natlist1 -> Prop,
                    P nnil1 ->
                    (forall (l : natlist1) (n : nat), P l -> P (nsnoc1 l n)) ->
                  forall n : natlist1, P n *)
(** [] *)



(** **** Exercise: 1 star, optional (byntree_ind)  *)
(** Write out the induction principle that Coq will generate for the
    following datatype.  Write down your answer on paper or type it
    into a comment, and then compare it with what Coq prints. *)

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
Check ExSet_ind.
(** [] *)



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
Inductive mytype (X:Type) : Type :=
  | constr1 : X -> mytype X
  | constr2 : nat -> mytype X
  | constr3 : mytype X -> nat -> mytype X.
Check mytype_ind.
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
  | quux : (nat -> foo X Y) -> foo X Y.
Check foo_ind.
(** reflexive type, see cpdt 3.6 *)
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
                    P f -> 
                    P (C1 X l f)   ) ->
             P (C2 X) ->
             forall f : foo' X, P f
*)
Check foo'_ind.
(** [] *)



(* ##################################################### *)
(** ** Induction Hypotheses *)

Definition P_m0r (n:nat) : Prop := 
  n * 0 = 0.

Definition P_m0r' : nat->Prop := 
  fun n => n * 0 = 0.

Theorem mult_0_r'' : forall n:nat, 
  P_m0r n.
Proof.
  apply nat_ind.
  Case "n = O". reflexivity.
  Case "n = S n'". 
    (* Note the proof state at this point! *)
    intros n IHn. 
    unfold P_m0r in IHn. unfold P_m0r. simpl. apply IHn. Qed.

(* ##################################################### *)
(** ** More on the [induction] Tactic *)

Theorem plus_assoc' : forall n m p : nat, 
  n + (m + p) = (n + m) + p.   
Proof.
  intros n m p. 
  induction n as [| n'].
  Case "n = O". reflexivity.
  Case "n = S n'". 
    simpl. rewrite -> IHn'. reflexivity.  Qed.

Theorem plus_comm' : forall n m : nat, 
  n + m = m + n.
Proof.
  induction n as [| n']. 
  Case "n = O". intros m. rewrite -> plus_0_r. reflexivity.
  Case "n = S n'". intros m. simpl. rewrite -> IHn'. 
    rewrite <- plus_n_Sm. reflexivity.  Qed.

Theorem plus_comm'' : forall n m : nat, 
  n + m = m + n.
Proof.
  induction m as [| m']. 
  Case "m = O". simpl. rewrite -> plus_0_r. reflexivity.
  Case "m = S m'". simpl. rewrite <- IHm'.
    rewrite <- plus_n_Sm. reflexivity.  Qed.



(** **** Exercise: 1 star, optional (plus_explicit_prop)  *)
(** Rewrite both [plus_assoc'] and [plus_comm'] and their proofs in
    the same style as [mult_0_r''] above -- that is, for each theorem,
    give an explicit [Definition] of the proposition being proved by
    induction, and state the theorem and proof in terms of this
    defined proposition.  *)

Definition P_pa (n m p : nat) : Prop :=
  n + (m + p) = (n + m) + p. 

Theorem plus_assoc'' : forall (n m p : nat),
  P_pa n m p.
Proof.
  intros n m p.
  induction n as [|n'].
  Case "n = O".
    reflexivity.
  Case "n = S n'".
    unfold P_pa in IHn'. unfold P_pa.
    simpl. rewrite IHn'. reflexivity.
Qed.

Definition P_pc (n m : nat) : Prop :=
  n + m = m + n.

Theorem plus_comm''' : forall n m : nat,
  P_pc n m.
Proof.
  intros n m.
  induction n as [|n'].
  Case "n = O".
    unfold P_pc. rewrite -> plus_0_r. reflexivity.
  Case "n = S n'".
    unfold P_pc in IHn'. unfold P_pc.
    simpl. rewrite IHn'. rewrite <- plus_n_Sm. reflexivity.
Qed.
(* FILL IN HERE *)
(** [] *)


(** ** Generalizing Inductions. *)

Lemma one_not_beautiful_FAILED: ~ beautiful 1. 
Proof.
  intro H.
  induction H. 
Abort.

Lemma one_not_beautiful: forall n, n = 1 -> ~ beautiful n. 
Proof.
 intros n E H.
  induction H  as [| | | p q Hp IHp Hq IHq]. 
    Case "b_0".
      inversion E.
    Case "b_3". 
      inversion E. 
    Case "b_5". 
      inversion E. 
    Case "b_sum". 
      destruct p as [|p'].
      SCase "p = 0".
        destruct q as [|q'].
        SSCase "q = 0". 
          inversion E.
        SSCase "q = S q'".
          apply IHq. apply E. 
      SCase "p = S p'". 
        destruct q as [|q'].
        SSCase "q = 0". 
          apply IHp.  rewrite plus_0_r in E. apply E. 
        SSCase "q = S q'".
          simpl in E. inversion E.  destruct p'.  inversion H0.  inversion H0. 
Qed.

Lemma one_not_beautiful': ~ beautiful 1. 
Proof.
  intros H.  
  remember 1 as n eqn:E. 
  induction H.   
Admitted.


(* ####################################################### *)
(** * Informal Proofs (Advanced) *)

(** ** Informal Proofs by Induction *)

(** *** Induction Over an Inductively Defined Set *)
 
(** *** Induction Over an Inductively Defined Proposition *)


(* ##################################################### *)
(** * Induction Principles in [Prop] (Advanced) *)

Check gorgeous_ind.

Theorem gorgeous__beautiful' : forall n, gorgeous n -> beautiful n.
Proof.
   intros.
   apply gorgeous_ind.
   Case "g_0".
       apply b_0.
   Case "g_plus3".
       intros.
       apply b_sum. apply b_3.
       apply H1.
   Case "g_plus5".
       intros.
       apply b_sum. apply b_5.
       apply H1.
   apply H.
Qed.

Inductive le (n:nat) : nat -> Prop :=
  | le_n : le n n
  | le_S : forall m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).

Check le_ind.


(* ##################################################### *)
(** * Additional Exercises *)



(** **** Exercise: 2 stars, optional (foo_ind_principle)  *)
(** Suppose we make the following inductive definition:
   Inductive foo (X : Set) (Y : Set) : Set :=
     | foo1 : X -> foo X Y
     | foo2 : Y -> foo X Y
     | foo3 : foo X Y -> foo X Y.
   Fill in the blanks to complete the induction principle that will be
   generated by Coq. 
   foo_ind
        : forall (X Y : Set) (P : foo X Y -> Prop),   
          (forall x : X, P (foo1 X Y x) ) ->
          (forall y : Y, P (foo2 X Y y) ) ->
          (forall f : foo X Y, P f -> P (foo3 X Y f) ) ->
           forall f : foo X Y, P f

*)
(** [] *)



(** **** Exercise: 2 stars, optional (bar_ind_principle)  *)
(** Consider the following induction principle:
   bar_ind
        : forall P : bar -> Prop,
          (forall n : nat, P (bar1 n)) ->
          (forall b : bar, P b -> P (bar2 b)) ->
          (forall (b : bool) (b0 : bar), P b0 -> P (bar3 b b0)) ->
          forall b : bar, P b
   Write out the corresponding inductive set definition.
   Inductive bar : Set :=
     | bar1 : nat -> bar
     | bar2 : bar -> bar
     | bar3 : bool -> bar -> bar.

*)
(** [] *)



(** **** Exercise: 2 stars, optional (no_longer_than_ind)  *)
(** Given the following inductively defined proposition:
  Inductive no_longer_than (X : Set) : (list X) -> nat -> Prop :=
    | nlt_nil  : forall n, no_longer_than X [] n
    | nlt_cons : forall x l n, no_longer_than X l n -> 
                               no_longer_than X (x::l) (S n)
    | nlt_succ : forall l n, no_longer_than X l n -> 
                             no_longer_than X l (S n).
  write the induction principle generated by Coq.
  no_longer_than_ind
       : forall (X : Set) (P : list X -> nat -> Prop),
         (forall n : nat, P X [] n ) ->
         (forall (x : X) (l : list X) (n : nat),
          no_longer_than X l n -> P X l n -> 
                                  P X (x::l) (S n) ->
         (forall (l : list X) (n : nat),
          no_longer_than X l n -> P X l n -> 
                                  P X l (S n) ->
         forall (l : list X) (n : nat), no_longer_than X l n -> 
           P X l n

*)
(** [] *)



(* ##################################################### *)
(** ** Induction Principles for other Logical Propositions *)

Inductive eq' (X:Type) (x:X) : X -> Prop :=
    refl_equal' : eq' X x x.

Check eq'_ind.



(** **** Exercise: 1 star, optional (and_ind_principle)  *)
(** See if you can predict the induction principle for conjunction. *)
(* Check and_ind. *)
(** [] *)

(** **** Exercise: 1 star, optional (or_ind_principle)  *)
(** See if you can predict the induction principle for disjunction. *)

(* Check or_ind. *)
(** [] *)

Check and_ind.



(** **** Exercise: 1 star, optional (False_ind_principle)  *)
(** Can you predict the induction principle for falsehood? *)

(* Check False_ind. *)
(** [] *)



Check ex_ind.


(* ######################################################### *)
(** ** Explicit Proof Objects for Induction *)

Check nat_ind.
Print nat_ind.
Print nat_rect.

 Definition nat_ind2 : 
    forall (P : nat -> Prop), 
    P 0 -> 
    P 1 -> 
    (forall n : nat, P n -> P (S(S n))) -> 
    forall n : nat , P n :=
       fun P => fun P0 => fun P1 => fun PSS => 
          fix f (n:nat) := match n with 
                             0 => P0 
                           | 1 => P1 
                           | S (S n') => PSS n' (f n') 
                          end.

Lemma even__ev' : forall n, even n -> ev n.
Proof. 
 intros.  
 induction n as [ | |n'] using nat_ind2. 
  Case "even 0". 
    apply ev_0.  
  Case "even 1". 
    inversion H.
  Case "even (S(S n'))". 
    apply ev_SS. 
    apply IHn'.  unfold even.  unfold even in H.  simpl in H. apply H. 
Qed. 

(* ######################################################### *)
(** ** The Coq Trusted Computing Base *)

(** $Date: 2014-12-31 15:31:47 -0500 (Wed, 31 Dec 2014) $ *)


