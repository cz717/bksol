
(** ** Chapter 5. Everyday Logic *)

(** Exercise 5.4 *)

Definition dyslexic_imp := forall P Q : Prop, (P -> Q) -> (Q -> P).
Definition dyslexic_contrap := forall P Q : Prop, (P -> Q) -> (~P -> ~Q).

Theorem dyimpf : dyslexic_imp -> False.
Proof.
  unfold dyslexic_imp.
  intros H. apply (H False True); trivial.
Qed.

Theorem dyctf : dyslexic_contrap -> False.
Proof.
  unfold dyslexic_contrap. unfold not.
  intros H. apply (H False True); trivial.
Qed.

(** [] *)


(** Exercise 5.7 *)

Definition classical := forall P : Prop, ~~P -> P.
Definition peirce := forall P Q: Prop, ((P -> Q) -> P) -> P.
Definition exclude_middle := forall P : Prop, P \/ ~P.
Definition de_morgan_not_and_not := forall P Q:Prop, ~(~P /\ ~Q) -> P\/Q.
Definition implies_to_or := forall P Q:Prop, (P -> Q) -> (~P \/ Q).

Theorem pe_to_cl :
  peirce -> classical.
Proof.
  unfold peirce. unfold classical.
  intros pe P NNP.
  apply (pe P False).
  intro NP.
  unfold not in NNP.
  destruct (NNP NP).
Qed.

Theorem cl_to_dm :
  classical -> de_morgan_not_and_not.
Proof.
  unfold classical.
  unfold de_morgan_not_and_not.
  intros cl P Q H.
  apply (cl (P \/ Q)).
  intro NPQ. apply H.
  split.
  - (* ~P *)
    intro HP. apply NPQ. left. apply HP.
  - (* ~Q *)
    intro HQ. apply NPQ. right. apply HQ.
Qed.

Theorem dm_to_ip :
  de_morgan_not_and_not -> implies_to_or.
Proof.
  unfold de_morgan_not_and_not.
  unfold implies_to_or.
  intros dm P Q HPQ.
  apply (dm (~P) Q).
  intros contra.
  destruct contra as [NNP NQ].
  apply NNP. intro HP.
  apply NQ. apply HPQ. apply HP.
Qed.


Theorem ip_to_em :
  implies_to_or -> exclude_middle.
Proof.
  unfold implies_to_or.
  unfold exclude_middle.
  intros ip P.
  cut (~P \/ P).
  - intros H. elim H; (right; assumption) || (left; assumption).
  - apply (ip P P); trivial.
Qed.


Theorem em_to_pe :
  exclude_middle -> peirce.
Proof.
  unfold exclude_middle. unfold peirce.
  intros em P Q H.
  destruct (em P) as [HP | NP].
  - assumption.
  - apply H. intros HP. elim (NP HP).
Qed.

(** [] *)


(** Exercise 5.9 *)

Section exer_9.

Variable A : Set.
Variable P Q : A -> Prop.

Theorem cont : (exists x:A, (forall R:A->Prop, R x)) -> 2 = 3.
Proof.
  intros H. destruct H as [x H].
  apply (H (fun a:A => 2 = 3)).
Qed.

Theorem neg : (forall x:A, P x) -> ~(exists y:A, ~ P y).
Proof.
  intros H. unfold not.
  intros H'. destruct H' as [y H'].
  apply H'. apply H.
Qed.

End exer_9.

(** [] *)


(** Exercise 5.10 *)

Require Import Arith.

Theorem plus_permute2 : forall n m p : nat, n+m+p = n+p+m.
Proof.
  intros n m p.
  rewrite <- plus_assoc.
  pattern (m+p). rewrite plus_comm.
  rewrite plus_assoc. reflexivity.
Qed.

(** [] *)


(** Exercise 5.11 *)

Theorem eq_trans : forall (A:Type) (x y z:A), x = y -> y = z -> x = z.
Proof.
  intros A x y z xy yz.
  apply (eq_ind y); assumption.
Qed.

(** [] *)


(** Exercise 5.13 *)

Definition my_False : Prop := forall P : Prop, P.
Definition my_not (P : Prop) : Prop := P -> my_False.

Theorem nf : my_not my_False.
Proof.
  unfold my_False, my_not.
  trivial.
Qed.

Theorem offset : forall P : Prop, my_not (my_not (my_not P)) -> my_not P.
Proof.
  unfold my_False, my_not. auto.
Qed.

Theorem ex3 : forall P Q : Prop,  my_not (my_not (my_not P)) -> P -> Q.
Proof.
  intros P Q H HP.
  apply (offset P H HP).
Qed.

Theorem ex4 : forall P Q : Prop, (P -> Q) -> my_not Q -> my_not P.
Proof.
  unfold my_not. intros P Q PQ NQ HP.
  apply NQ. apply PQ. assumption.
Qed.

Theorem ex5 : forall P Q R : Prop, (P -> Q) -> (P -> my_not Q) -> P -> R.
Proof.
  unfold my_not. intros P Q R PQ PNQ HP.
  apply (PNQ HP (PQ HP)).
Qed.

(** [] *)


Section leibniz.
Set Implicit Arguments.
Unset Strict Implicit.
Variable A : Set.

Definition leibniz (a b : A) : Prop :=
  forall (P : A -> Prop), P a -> P b.

Require Import Relations.

Theorem leibniz_sym : symmetric A leibniz.
Proof.
  unfold symmetric, leibniz.
  intros x y H P.
  apply H. trivial.
Qed.


(** Exercise 5.14 *)

Theorem leibniz_refl : reflexive A leibniz.
Proof.
  unfold reflexive, leibniz. trivial.
Qed.

Theorem leibniz_trans : transitive A leibniz.
Proof.
  unfold transitive, leibniz.
  intros x y z xy yz.
  apply yz. apply xy.
Qed.

Theorem leibniz_equiv : equiv A leibniz.
Proof.
  unfold equiv. repeat split.
  exact leibniz_refl.
  exact leibniz_trans.
  exact leibniz_sym.
Qed.

Theorem leibniz_least_reflexive : forall R:relation A, 
  reflexive A R -> inclusion A leibniz R.
Proof.
  unfold inclusion, reflexive, leibniz.
  intros R RA x y E.
  apply E. apply RA.
Qed.

Theorem leibniz_eq : forall a b:A, leibniz a b -> a = b.
Proof.
  unfold leibniz. intros a b E.
  apply E. reflexivity.
Qed.

Theorem eq_leibniz : forall a b:A, a = b -> leibniz a b.
Proof.
  unfold leibniz. intros a b E P PA.
  rewrite <- E. assumption.
Qed.

Theorem leibniz_ind : forall (x : A) (P : A -> Prop), 
  P x -> forall y : A, leibniz x y -> P y.
Proof.
  unfold leibniz. intros x P PX y E.
  apply E. assumption.
Qed.

Unset Implicit Arguments.
End leibniz.

(** [] *)


Definition my_le (n p : nat) : Prop :=
  forall P : nat -> Prop, P n -> 
    (forall q : nat, P q -> P (S q)) -> P p.

(** Exercise 5.16 *)

Lemma my_le_n : forall n : nat, my_le n n.
Proof.
  unfold my_le. intros n P Pn H.
  assumption.
Qed.

Lemma my_le_S : forall n p : nat, my_le n p -> my_le n (S p).
Proof.
  unfold my_le.
  intros n p NP P Pn H.
  apply H. apply NP; assumption.
Qed.

Lemma my_le_le : forall n p : nat, my_le n p -> n <= p.
Proof.
  unfold my_le. intros n p H.
  apply H.
  - apply le_n.
  - apply le_S.
Qed.

(** [] *)
