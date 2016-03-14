
(** * Rel: Properties of Relations *)

Require Export IndProp.

Definition relation (X: Type) := X->X->Prop.

Print le.
Check le : nat -> nat -> Prop.
Check le : relation nat.

(* ######################################################### *)
(** * Basic Properties of Relations *)

Definition partial_function {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Print next_nat.
Check next_nat : relation nat.

Theorem next_nat_partial_function :
   partial_function next_nat.
Proof.
  unfold partial_function.
  intros x y1 y2 H1 H2.
  inversion H1. inversion H2.
  reflexivity.  Qed.

Theorem le_not_a_partial_function :
  ~ (partial_function le).
Proof.
  unfold not. unfold partial_function. intros Hc.
  assert (0 = 1) as Nonsense.
  { (* Proof of assertion *)
    apply Hc with (x := 0).
    - apply le_n.
    - apply le_S. apply le_n. }
  inversion Nonsense.   Qed.

(** **** Exercise: 2 stars, optional  *)
(** Show that the [total_relation] defined in earlier is not a partial
    function. *)

Theorem total_relation_not_a_partial_function :
  ~ (partial_function total_relation).
Proof.
  unfold not. unfold partial_function. intros H.
  assert (0 = 1) as N.
  { apply (H 0); apply tr. } 
  inversion N.
Qed.

(** [] *)

(** **** Exercise: 2 stars, optional  *)
(** Show that the [empty_relation] defined earlier is a partial
    function. *)
Theorem empty_relation_partial_function :
  partial_function empty_relation.
Proof.
  unfold partial_function.
  intros x y1 y2 H1 H2.
  inversion H1.
Qed.
(** [] *)


Definition reflexive {X: Type} (R: relation X) :=
  forall a : X, R a a.

Theorem le_reflexive :
  reflexive le.
Proof.
  unfold reflexive. intros n. apply le_n.  Qed.


Definition transitive {X: Type} (R: relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).

Theorem le_trans :
  transitive le.
Proof.
  intros n m o Hnm Hmo.
  induction Hmo.
  - (* le_n *) apply Hnm.
  - (* le_S *) apply le_S. apply IHHmo.  Qed.

Theorem lt_trans:
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  apply le_S in Hnm.
  apply le_trans with (a := (S n)) (b := (S m)) (c := o).
  apply Hnm.
  apply Hmo. Qed.

(** **** Exercise: 2 stars, optional  *)
(** We can also prove [lt_trans] more laboriously by induction,
    without using le_trans.  Do this.*)

Theorem lt_trans' :
  transitive lt.
Proof.
  (* Prove this by induction on evidence that [m] is less than [o]. *)
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction Hmo as [| m' Hm'o].
  - (* S m = o *)
    apply le_S. apply Hnm.
  - (* S m < o *) 
    apply le_S. apply IHHm'o.
Qed.

(** [] *)


(** **** Exercise: 2 stars, optional  *)
(** Prove the same thing again by induction on [o]. *)

Theorem lt_trans'' :
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction o as [| o'].
  - (* o = 0 *)
    inversion Hmo.
  - (* o = S o' *)
    inversion Hmo as [E | m' H IH ].
    + (* m = o' *)
      apply le_S. rewrite <- E. assumption.
    + (* m < o' *)
      apply le_S. apply IHo'. apply H.
Qed.

(** [] *)

Theorem le_Sn_le : forall n m, S n <= m -> n <= m.
Proof.
  intros n m H. apply le_trans with (S n).
    apply le_S. apply le_n.
    apply H.  Qed.

(** **** Exercise: 1 star, optional  *)
Theorem le_S_n : forall n m,
  (S n <= S m) -> (n <= m).
Proof.
  intros n m H.
  inversion H as [E | m' H' IH].
  - apply le_n.
  - apply le_Sn_le. assumption.
Qed.
(** [] *)

(** **** Exercise: 2 stars, optional (le_Sn_n_inf)  *)
(** Provide an informal proof of the following theorem:

    Theorem: For every [n], [~(S n <= n)]

    A formal proof of this is an optional exercise below, but try
    the informal proof without doing the formal proof first.

    Proof:
    (* FILL IN HERE *)
    []
 *)

(** **** Exercise: 1 star, optional  *)
Theorem le_Sn_n : forall n,
  ~ (S n <= n).
Proof.
  unfold not. 
  induction n as [|n'].
  - (* n = 0 *) 
    intros H. inversion H.
  - (* n = S n' *)
    intros H. apply IHn'.
    apply le_S_n. apply H.
Qed.

(** [] *)


Definition symmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a).

(** **** Exercise: 2 stars, optional  *)
Theorem le_not_symmetric :
  ~ (symmetric le).
Proof.
  unfold not. unfold symmetric. intros S. 
  assert (N: 1 <= 0 -> False).
  { apply (le_Sn_n 0). }
  apply N. apply S. apply le_S. apply le_n.
Qed.

(** [] *)


Definition antisymmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a) -> a = b.

(** **** Exercise: 2 stars, optional  *)
Theorem le_antisymmetric :
  antisymmetric le.
Proof.
  unfold antisymmetric.
  induction a as [|a'].
  - (* a = 0 *)
    intros b ab ba.
    inversion ba as [E|].
    reflexivity.
  - (* a = S a' *)
    intros b ab ba.
    inversion ab as [E | b' H H'].
    + (* a = b *)
      reflexivity.
    + (* a < b *)
      cut (a' = b').
      * intros E. rewrite E. reflexivity.
      * apply IHa'. 
        { apply le_Sn_le. apply H. }
        { apply le_S_n. rewrite H'. apply ba. }
Qed.
      
(** [] *)

(** **** Exercise: 2 stars, optional  *)
Theorem le_step : forall n m p,
  n < m ->
  m <= S p ->
  n <= p.
Proof.
  intros n m p nm mp.
  unfold lt in nm. 
  apply le_S_n. 
  apply (le_trans (S n) m (S p) nm mp).
Qed.

(** [] *)


Definition equivalence {X:Type} (R: relation X) :=
  (reflexive R) /\ (symmetric R) /\ (transitive R).

Definition order {X:Type} (R: relation X) :=
  (reflexive R) /\ (antisymmetric R) /\ (transitive R).

Definition preorder {X:Type} (R: relation X) :=
  (reflexive R) /\ (transitive R).

Theorem le_order :
  order le.
Proof.
  unfold order. split.
    - (* refl *) apply le_reflexive.
    - split.
      + (* antisym *) apply le_antisymmetric.
      + (* transitive. *) apply le_trans.  Qed.

(* ########################################################### *)
(** * Reflexive, Transitive Closure *)

(** The _reflexive, transitive closure_ of a relation [R] is the
    smallest relation that contains [R] and that is both reflexive and
    transitive.  Formally, it is defined like this in the Relations
    module of the Coq standard library: *)

Inductive clos_refl_trans {A: Type} (R: relation A) : relation A :=
    | rt_step : forall x y, R x y -> clos_refl_trans R x y
    | rt_refl : forall x, clos_refl_trans R x x
    | rt_trans : forall x y z,
          clos_refl_trans R x y ->
          clos_refl_trans R y z ->
          clos_refl_trans R x z.


Theorem next_nat_closure_is_le : forall n m,
  (n <= m) <-> ((clos_refl_trans next_nat) n m).
Proof.
  intros n m. split.
    - (* -> *)
      intro H. induction H.
      + (* le_n *) apply rt_refl.
      + (* le_S *)
        apply rt_trans with m. apply IHle. apply rt_step. apply nn.
    - (* <- *)
      intro H. induction H.
      + (* rt_step *) inversion H. apply le_S. apply le_n.
      + (* rt_refl *) apply le_n.
      + (* rt_trans *)
        apply le_trans with y.
        apply IHclos_refl_trans1.
        apply IHclos_refl_trans2. Qed.


Inductive clos_refl_trans_1n {A : Type}
                             (R : relation A) (x : A)
                             : A -> Prop :=
  | rt1n_refl : clos_refl_trans_1n R x x
  | rt1n_trans (y z : A) :
      R x y -> clos_refl_trans_1n R y z ->
      clos_refl_trans_1n R x z.


Theorem rsc_R : forall (X:Type) (R:relation X) (x y : X),
       R x y -> clos_refl_trans_1n R x y.
Proof.
  intros X R x y H.
  apply rt1n_trans with y. apply H. apply rt1n_refl.   Qed.

(** **** Exercise: 2 stars, optional (rsc_trans)  *)
Theorem rsc_trans :
  forall (X:Type) (R: relation X) (x y z : X),
      clos_refl_trans_1n R x y  ->
      clos_refl_trans_1n R y z ->
      clos_refl_trans_1n R x z.
Proof.
  intros X R x y z xy.
  generalize dependent z.
  induction xy as [| x y' y H H' IH].
  - trivial.
  - intros z yz.
    apply (rt1n_trans R x y' z).
    + assumption.
    + apply IH. assumption.
Qed.

(** [] *)


(** **** Exercise: 3 stars, optional (rtc_rsc_coincide)  *)
Theorem rtc_rsc_coincide :
         forall (X:Type) (R: relation X) (x y : X),
  clos_refl_trans R x y <-> clos_refl_trans_1n R x y.
Proof.
  intros X R x y.
  split.
  { intros C. induction C as [x' y' Rxy | x' E | x' y' z' Cxy IH1 Cyz IH2 ].
    { apply rsc_R. apply Rxy. }
    { apply rt1n_refl. }
    { apply rsc_trans with (y:= y'); assumption. } }
  { intros C1. induction C1 as [x' E | x' y' z' Rxy C1yz IH ].
    { apply rt_refl. }
    { apply rt_trans with (y:= y').
      - apply rt_step. apply Rxy. 
      - apply IH. } } 
Qed.

(** [] *)

(** $Date: 2016-02-17 17:39:13 -0500 (Wed, 17 Feb 2016) $ *)
