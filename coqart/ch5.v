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


