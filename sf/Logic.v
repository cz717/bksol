(** * Logic: Logic in Coq *)

Require Export MoreCoq. 

(* ########################################################### *)
(** * Propositions *)

Check (3 = 3).

Check (forall (n:nat), n = 2).

(* ########################################################### *)
(** * Proofs and Evidence *)

Lemma silly : 0 * 3 = 0.
Proof. reflexivity. Qed.

Print silly.

Lemma silly_implication : (1 + 1) = 2  ->  0 * 3 = 0.
Proof. intros H. reflexivity. Qed.

Print silly_implication.

(* ########################################################### *)
(** * Conjunction (Logical "and") *)

Inductive and (P Q : Prop) : Prop :=
  conj : P -> Q -> (and P Q). 

Notation "P /\ Q" := (and P Q) : type_scope.

Check conj.

(** ** "Introducing" conjunctions *)

Theorem and_example : 
  (0 = 0) /\ (4 = mult 2 2).
Proof.
  apply conj.
  Case "left". reflexivity.
  Case "right". reflexivity.  Qed.

Theorem and_example' : 
  (0 = 0) /\ (4 = mult 2 2).
Proof.
  split.
    Case "left". reflexivity.
    Case "right". reflexivity.  Qed.

(** ** "Eliminating" conjunctions *)

Theorem proj1 : forall P Q : Prop, 
  P /\ Q -> P.
Proof.
  intros P Q H.
  destruct H as [HP HQ]. 
  apply HP.  Qed.



(** **** Exercise: 1 star, optional (proj2)  *)
Theorem proj2 : forall P Q : Prop, 
  P /\ Q -> Q.
Proof.
  intros P Q H.
  destruct H as [HP HQ]. 
  apply HQ. 
Qed.
(** [] *)



Theorem and_commut : forall P Q : Prop, 
  P /\ Q -> Q /\ P.
Proof.
  intros P Q H.
  destruct H as [HP HQ]. 
  split.  
    Case "left". apply HQ. 
    Case "right". apply HP.  Qed.
  


(** **** Exercise: 2 stars (and_assoc)  *)
(** In the following proof, notice how the _nested pattern_ in the
    [destruct] breaks the hypothesis [H : P /\ (Q /\ R)] down into
    [HP: P], [HQ : Q], and [HR : R].  Finish the proof from there: *)

Theorem and_assoc : forall P Q R : Prop, 
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R H.
  destruct H as [HP [HQ HR]].
  split.
  split. apply HP. apply HQ.
  apply HR.
Qed.
(** [] *)



(* ###################################################### *)
(** * Iff *)

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q) 
                      (at level 95, no associativity) 
                      : type_scope.

Theorem iff_implies : forall P Q : Prop, 
  (P <-> Q) -> P -> Q.
Proof.  
  intros P Q H. 
  destruct H as [HAB HBA]. apply HAB.  Qed.

Theorem iff_sym : forall P Q : Prop, 
  (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q H. 
  destruct H as [HAB HBA].
  split.
    Case "->". apply HBA.
    Case "<-". apply HAB.  Qed.



(** **** Exercise: 1 star, optional (iff_properties)  *)
(** Using the above proof that [<->] is symmetric ([iff_sym]) as
    a guide, prove that it is also reflexive and transitive. *)

Theorem iff_refl : forall P : Prop, 
  P <-> P.
Proof. 
  intro P.
  split.
  intro p. apply p.
  intro p. apply p.
Qed.


Theorem iff_trans : forall P Q R : Prop, 
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R.
  intros HPQ HQR.
  inversion HPQ. inversion HQR.
  split.
  Case "P -> R".
    intro p. apply H1. apply H. apply p.
  Case "R -> P".
    intro r. apply H0. apply H2. apply r.
Qed.

(** Hint: If you have an iff hypothesis in the context, you can use
    [inversion] to break it into two separate implications.  (Think
    about why this works.) *)
(** [] *)



(* ############################################################ *)
(** * Disjunction (Logical "or") *)

(** ** Implementing disjunction *)

Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q. 

Notation "P \/ Q" := (or P Q) : type_scope.

Check or_introl.

Check or_intror.

Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros P Q H.
  destruct H as [HP | HQ].
    Case "left". apply or_intror. apply HP.
    Case "right". apply or_introl. apply HQ.  Qed.

Theorem or_commut' : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros P Q H.
  destruct H as [HP | HQ].
    Case "left". right. apply HP.
    Case "right". left. apply HQ.  Qed.

Theorem or_distributes_over_and_1 : forall P Q R : Prop,
  P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof. 
  intros P Q R. intros H. destruct H as [HP | [HQ HR]]. 
    Case "left". split.
      SCase "left". left. apply HP.
      SCase "right". left. apply HP.
    Case "right". split.
      SCase "left". right. apply HQ.
      SCase "right". right. apply HR.  Qed.



(** **** Exercise: 2 stars (or_distributes_over_and_2)  *)
Theorem or_distributes_over_and_2 : forall P Q R : Prop,
  (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
  intros P Q R. intro H.
  destruct H as [[HP|HQ] [HP'|HR]].
  Case "P".
    left. apply HP.
  Case "P R".
    left. apply HP.
  Case "Q P".
    left. apply HP'.
  Case "Q R".
    right. 
    split. apply HQ. apply HR.
Qed.
(** [] *)



(** **** Exercise: 1 star, optional (or_distributes_over_and)  *)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  split.
  apply or_distributes_over_and_1.
  apply or_distributes_over_and_2.
Qed.
(** [] *)



(* ################################################### *)
(** ** Relating [/\] and [\/] with [andb] and [orb] *)

Theorem andb_prop : forall b c,
  andb b c = true -> b = true /\ c = true.
Proof.
  intros b c H.
  destruct b.
    Case "b = true". destruct c.
      SCase "c = true". apply conj. reflexivity. reflexivity.
      SCase "c = false". inversion H.
    Case "b = false". inversion H.  Qed.

Theorem andb_true_intro : forall b c,
  b = true /\ c = true -> andb b c = true.
Proof.
  intros b c H.
  destruct H.
  rewrite H. rewrite H0. reflexivity. Qed.



(** **** Exercise: 2 stars, optional (andb_false)  *)
Theorem andb_false : forall b c,
  andb b c = false -> b = false \/ c = false.
Proof. 
  intros b c H.
  destruct b.
  Case "b = true".
    destruct c.
    SCase "c = true". inversion H.
    SCase "c = false". right. reflexivity.
  Case "b = false".
    left. reflexivity.
Qed.



(** **** Exercise: 2 stars, optional (orb_false)  *)
Theorem orb_prop : forall b c,
  orb b c = true -> b = true \/ c = true.
Proof.
  intros b c H.
  destruct b.
  Case "b = true".
    left. reflexivity.
  Case "b = false".
    destruct c.
    SCase "c = true".
      right. reflexivity.
    SCase "c = false".
      inversion H.
Qed.



(** **** Exercise: 2 stars, optional (orb_false_elim)  *)
Theorem orb_false_elim : forall b c,
  orb b c = false -> b = false /\ c = false.
Proof. 
  intros b c H.
  destruct b.
  Case "b = true". inversion H.
  Case "b = false".
    destruct c.
    SCase "c = true". inversion H.
    SCase "c = false".
      split. reflexivity. reflexivity.
Qed.
(** [] *)



(* ################################################### *)
(** * Falsehood *)

Inductive False : Prop := . 

Theorem False_implies_nonsense :
  False -> 2 + 2 = 5.
Proof. 
  intros contra.
  inversion contra.  Qed. 

Theorem nonsense_implies_False :
  2 + 2 = 5 -> False.
Proof.
  intros contra.
  inversion contra.  Qed.

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros P contra.
  inversion contra.  Qed.

(* #################################################### *)
(** ** Truth *)

(** **** Exercise: 2 stars, advanced (True)  *)
(** Define [True] as another inductively defined proposition.  (The
    intution is that [True] should be a proposition for which it is
    trivial to give evidence.) *)
Print True.
(* FILL IN HERE *)
(** [] *)



(* #################################################### *)
(** * Negation *)

Definition not (P:Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.

Check not.

Theorem not_False : 
  ~ False.
Proof.
  unfold not. intros H. inversion H.  Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof. 
  intros P Q H. destruct H as [HP HNA]. unfold not in HNA. 
  apply HNA in HP. inversion HP.  Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  intros P H. unfold not. intros G. apply G. apply H.  Qed.



(** **** Exercise: 2 stars, advanced (double_neg_inf)  *)
(** Write an informal proof of [double_neg]:

   _Theorem_: [P] implies [~~P], for any proposition [P].

   _Proof_:
(* FILL IN HERE *)
   []
*)



(** **** Exercise: 2 stars (contrapositive)  *)
Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q HPQ NQ.
  unfold not. intro HP.
  apply NQ. apply HPQ. apply HP.
Qed.
(** [] *)



(** **** Exercise: 1 star (not_both_true_and_false)  *)
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof. 
  intro P.
  unfold not. intro PNP.
  destruct PNP as [HP NP].
  apply NP. apply HP.
Qed.
(** [] *)



(** **** Exercise: 1 star, advanced (informal_not_PNP)  *)
(** Write an informal proof (in English) of the proposition [forall P
    : Prop, ~(P /\ ~P)]. *)

(* FILL IN HERE *)
(** [] *)



(** *** Constructive logic *)

Theorem classic_double_neg : forall P : Prop,
  ~~P -> P.
Proof.
  intros P H. unfold not in H. 
  Abort.



(** **** Exercise: 5 stars, advanced, optional (classical_axioms)  *)
(** For those who like a challenge, here is an exercise
    taken from the Coq'Art book (p. 123).  The following five
    statements are often considered as characterizations of
    classical logic (as opposed to constructive logic, which is
    what is "built in" to Coq).  We can't prove them in Coq, but
    we can consistently add any one of them as an unproven axiom
    if we wish to work in classical logic.  Prove that these five
    propositions are equivalent. *)

Definition peirce := forall P Q: Prop, 
  ((P->Q)->P)->P.
Definition classic := forall P:Prop, 
  ~~P -> P.
Definition excluded_middle := forall P:Prop, 
  P \/ ~P.
Definition de_morgan_not_and_not := forall P Q:Prop, 
  ~(~P /\ ~Q) -> P\/Q.
Definition implies_to_or := forall P Q:Prop, 
  (P->Q) -> (~P\/Q). 

(* prove the equivalent by proving a ring :
   pe -> cl -> dm -> ip -> em -> pe
*)

Theorem pe_to_cl :
  peirce -> classic.
Proof.
  unfold peirce. unfold classic.
  intros pe P NNP.
  apply (pe P False).
  intro NP.
  unfold not in NNP.
  destruct (NNP NP).
Qed.

Theorem cl_to_dm :
  classic -> de_morgan_not_and_not.
Proof.
  unfold classic.
  unfold de_morgan_not_and_not.
  intros cl P Q H.
  apply (cl (P \/ Q)).
  intro NPQ. apply H.
  split.
  Case "~P".
    intro HP. apply NPQ. left. apply HP.
  Case "~Q".
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
  implies_to_or -> excluded_middle.
Proof.
  unfold implies_to_or.
  unfold excluded_middle.
  intros ip P.
  apply (or_commut (~P) P).
  apply (ip P).
  intro HP. apply HP.
Qed.

Theorem em_to_pe :
  excluded_middle -> peirce.
Proof.
  unfold excluded_middle.
  unfold peirce.
  intros em P Q. intro H.
  destruct (em P).
  Case "P".
   apply H0.
 Case "~P".
   apply H. intro HP.
   destruct (H0 HP).
Qed.
(* done *)


Theorem em_to_cl :
  excluded_middle -> classic.
Proof.
  unfold excluded_middle.
  unfold classic.
  intros em P NNP.
  destruct (em P) as [HP|NP].
  Case "P".
    apply HP.
  Case "~P".
    apply ex_falso_quodlibet.
    apply NNP. apply NP.
Qed.

Theorem cl_to_pe :
  classic -> peirce.
Proof.
  unfold classic. unfold peirce.
  intros cl P Q. intro H.
  apply (cl P).
  intro NP. apply NP.
  apply H. intro HP.
  apply ex_falso_quodlibet.
  apply (NP HP).
Qed.

Theorem em_to_im :
  excluded_middle -> implies_to_or.
Proof.
  unfold excluded_middle.
  unfold implies_to_or.
  intros em P Q HPQ.
  destruct (em P) as [HP|NP].
  Case "P".
    right. apply HPQ. apply HP.
  Case "~P".
    left. apply NP.
Qed.

Theorem dm_to_em :
  de_morgan_not_and_not -> excluded_middle.
Proof.
  unfold de_morgan_not_and_not.
  unfold excluded_middle.
  intros dm P.
  apply (dm P (not P)).
  intro contra.
  destruct contra as [NP NNP].
  apply NNP. apply NP.
Qed.


(* FILL IN HERE *)
(** [] *)



(** **** Exercise: 3 stars (excluded_middle_irrefutable)  *)
(** This theorem implies that it is always safe to add a decidability
axiom (i.e. an instance of excluded middle) for any _particular_ Prop [P].
Why? Because we cannot prove the negation of such an axiom; if we could,
we would have both [~ (P \/ ~P)] and [~ ~ (P \/ ~P)], a contradiction. *)

Theorem excluded_middle_irrefutable:  forall (P:Prop), ~ ~ (P \/ ~ P).  
Proof.
  intro P. unfold not. 
  
  (* FILL IN HERE *) Admitted.



(* ########################################################## *)
(** ** Inequality *)

Notation "x <> y" := (~ (x = y)) : type_scope.

Theorem not_false_then_true : forall b : bool,
  b <> false -> b = true.
Proof.
  intros b H. destruct b.
  Case "b = true". reflexivity.
  Case "b = false".
    unfold not in H.  
    apply ex_falso_quodlibet.
    apply H. reflexivity.   Qed.



(** **** Exercise: 2 stars (false_beq_nat)  *)
Theorem false_beq_nat : forall n m : nat,
     n <> m ->
     beq_nat n m = false.
Proof.
  intros n.
  induction n as [|n'].
  Case "n = 0".
    intros m H.
    induction m as [|m'].
    SCase "m = 0". 
      apply ex_falso_quodlibet. apply H. reflexivity.
    SCase "m = S m'". 
      reflexivity.
  Case "n = S n'".
    intros m H.
    destruct m as [|m'].
    SCase "m = 0".
      reflexivity.
    SCase "m = S m'".
      simpl. apply IHn'.
      unfold not. intro Hn'm'.
      apply H. rewrite Hn'm'. reflexivity.
Qed.
(** [] *)



(** **** Exercise: 2 stars, optional (beq_nat_false)  *)
Theorem beq_nat_false : forall n m,
  beq_nat n m = false -> n <> m.
Proof.
  intro n.
  induction n as [|n'].
  Case "n = 0".
    intros m H.
    destruct m as [|m'].
    SCase "m = 0". 
      inversion H.
    SCase "m = S m'".
      intro contra. inversion contra.
  Case "n = S n'".
    intros m H.
    destruct m as [|m'].
    SCase "m = 0".
      intro contra. inversion contra.
    SCase "m = S m'".
      simpl in H. apply IHn' in H.
      intro contra. apply H. inversion contra. reflexivity.
Qed.
(** [] *)


(** $Date: 2014-12-31 11:17:56 -0500 (Wed, 31 Dec 2014) $ *)

