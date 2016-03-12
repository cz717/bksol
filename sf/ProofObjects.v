(** * ProofObjects: The Curry-Howard Correspondence *)

(** "_Algorithms are the computational  content of proofs_."  --Robert Harper *)

Require Export IndProp.

Print ev.

Check ev_SS.

Theorem ev_4 : ev 4.
Proof.
  apply ev_SS. apply ev_SS. apply ev_0. Qed.

Print ev_4.

Check (ev_SS 2 (ev_SS 0 ev_0)).

Theorem ev_4': ev 4.
Proof.
  apply (ev_SS 2 (ev_SS 0 ev_0)).
Qed.

(* ##################################################### *)
(** * Proof Scripts *)

Theorem ev_4'' : ev 4.
Proof.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_0.
  Show Proof.
Qed.

Definition ev_4''' : ev 4 :=
  ev_SS 2 (ev_SS 0 ev_0).

Print ev_4.
Print ev_4'.
Print ev_4''.
Print ev_4'''.


(** **** Exercise: 1 star (eight_is_even)  *)
(** Give a tactic proof and a proof object showing that [ev 8]. *)

Theorem ev_8 : ev 8.
Proof.
  repeat apply ev_SS; apply ev_0.
  Show Proof.
Qed.

Definition ev_8' : ev 8 :=
  ev_SS 6 (ev_SS 4 (ev_SS 2 (ev_SS 0 ev_0))).

(** [] *)

(* ##################################################### *)
(** * Quantifiers, Implications, Functions *)

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n H. simpl.
  apply ev_SS.
  apply ev_SS.
  apply H.
Qed.

Definition ev_plus4' : forall n, ev n -> ev (4 + n) :=
  fun (n : nat) => fun (H : ev n) =>
    ev_SS (S (S n)) (ev_SS n H).

Check ev_plus4'.

Definition ev_plus4'' (n : nat) (H : ev n) : ev (4 + n) :=
  ev_SS (S (S n)) (ev_SS n H).

Check ev_plus4''.

Definition ev_plus2 : Prop :=
  forall n, forall (E : ev n), ev (n + 2).

Definition ev_plus2' : Prop :=
  forall n, forall (_ : ev n), ev (n + 2).

Definition ev_plus2'' : Prop :=
  forall n, ev n -> ev (n + 2).


(* ###################################################################### *)
(** * Connectives as Inductive Types *)

Module Props.

Module And.

Inductive and (P Q : Prop) : Prop :=
| conj : P -> Q -> and P Q.

End And.

Print prod.

Lemma and_comm : forall P Q : Prop, P /\ Q <-> Q /\ P.
Proof.
  intros P Q. split.
  - intros [HP HQ]. split.
    + apply HQ.
    + apply HP.
  - intros [HP HQ]. split.
    + apply HQ.
    + apply HP.
Qed.

Definition and_comm'_aux P Q (H : P /\ Q) :=
  match H with
  | conj HP HQ => conj HQ HP
  end.

Definition and_comm' P Q : P /\ Q <-> Q /\ P :=
  conj (and_comm'_aux P Q) (and_comm'_aux Q P).

(** **** Exercise: 2 stars, optional (conj_fact)  *)
(** Construct a proof object demonstrating the following proposition. *)

Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
  fun P Q R (PQ:P/\Q) (QR:Q/\R) =>
    match PQ with
      | conj HP HQ => match QR with
                        | conj HQ HR => conj HP HR
                      end
    end.

(** [] *)

(** ** Disjunction *)

Module Or.

Inductive or (P Q : Prop) : Prop :=
| or_introl : P -> or P Q
| or_intror : Q -> or P Q.


End Or.

(** **** Exercise: 2 stars, optional (or_commut'')  *)
(** Try to write down an explicit proof object for [or_commut] (without
    using [Print] to peek at the ones we already defined!). *)

Definition or_comm : forall P Q, P \/ Q -> Q \/ P :=
  fun P Q (PQ:P\/Q) =>
    match PQ with
      | or_introl HP => or_intror HP
      | or_intror HQ => or_introl HQ
    end.

(** [] *)

(** ** Existential *)

Module Ex.

Inductive ex {A : Type} (P : A -> Prop) : Prop :=
| ex_intro : forall x : A, P x -> ex P.

End Ex.

Check ex (fun n => ev n).

Definition some_nat_is_even : exists n, ev n :=
  ex_intro ev 4 (ev_SS 2 (ev_SS 0 ev_0)).

(** **** Exercise: 2 stars, optional (ex_ev_Sn)  *)
(** Complete the definition of the following proof object: *)

Definition ex_ev_Sn : ex (fun n => ev (S n)) :=
  ex_intro (fun n => ev (S n)) 1 (ev_SS 0 ev_0).
(** [] *)

(** ** [True] and [False] *)

Inductive True : Prop :=
  I : True.

Inductive False : Prop :=.

End Props.

(* ##################################################### *)
(** * Programming with Tactics *)

Definition add1 : nat -> nat.
intro n.
Show Proof.
apply S.
Show Proof.
apply n. Defined.

Print add1.

Compute add1 2.

(* ###################################################### *)
(** * Equality *)

Module MyEquality.

Inductive eq {X:Type} : X -> X -> Prop :=
| eq_refl : forall x, eq x x.

Notation "x = y" := (eq x y)
                    (at level 70, no associativity)
                    : type_scope.

(** **** Exercise: 2 stars (leibniz_equality)  *)
(** The inductive definition of equality corresponds to _Leibniz
    equality_: what we mean when we say "[x] and [y] are equal" is
    that every property on [P] that is true of [x] is also true of
    [y].  *)

Lemma leibniz_equality : forall (X : Type) (x y: X),
  x = y -> forall P:X->Prop, P x -> P y.
Proof.
  intros X x y E P Px.
  destruct E. assumption.
Qed.

(** [] *)

Lemma four: 2 + 2 = 1 + 3.
Proof.
  apply eq_refl.
Qed.

Definition four' : 2 + 2 = 1 + 3 :=
  eq_refl 4.

Definition singleton : forall (X:Set) (x:X), []++[x] = x::[]  :=
  fun (X:Set) (x:X) => eq_refl [x].


End MyEquality.

Definition quiz6 : exists x,  x + 3 = 4
  := ex_intro (fun z => (z + 3 = 4)) 1 (refl_equal 4).

(* ####################################################### *)
(** ** Inversion, Again *)

(** $Date: 2016-02-17 17:39:13 -0500 (Wed, 17 Feb 2016) $ *)

