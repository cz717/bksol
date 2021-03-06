(* Lazy lists . P. Cast�ran after Eduardo Gimenez *)
(**************************************************)
Require Import Arith.
Set Implicit Arguments.

CoInductive LList (A:Set) : Set :=
  | LNil : LList A
  | LCons : A -> LList A -> LList A.

Implicit Arguments LNil [A].

CoInductive LTree (A : Set) : Set :=
   LLeaf :  LTree A
 | LBin : A -> LTree A -> LTree A -> LTree A.

Implicit Arguments LLeaf [A].


(** Exercise 13.1 *)

Fixpoint tol (A : Set)(l : list A) : LList A :=
  match l with
    | nil => LNil
    | cons h t => LCons h (tol t)
  end.

Theorem tol_inj : forall (A : Set) (l0 l1 : list A), 
  tol l0 = tol l1 -> l0 = l1.
Proof. 
  intros A l0.
  induction l0 as [|h0 t0]; intros l1 H. 
  - destruct l1. 
    + reflexivity. 
    + simpl in H. discriminate H. 
  - destruct l1 as [|h1 t1].
    + simpl in H. discriminate H. 
    + simpl in H. injection H. 
      intros H0 H1.
      rewrite (IHt0 t1 H0).
      rewrite H1. reflexivity. 
Qed.

(** [] *)


Definition isEmpty (A:Set) (l:LList A) : Prop :=
  match l with
  | LNil => True
  | LCons a l' => False
  end.

Definition LHead (A:Set) (l:LList A) : option A :=
  match l with
  | LNil => None 
  | LCons a l' => Some a
  end.

Definition LTail (A:Set) (l:LList A) : LList A :=
  match l with
  | LNil => LNil 
  | LCons a l' => l'
  end.

Fixpoint LNth (A:Set) (n:nat) (l:LList A) {struct n} : 
 option A :=
  match l with
  | LNil => None 
  | LCons a l' => match n with
                  | O => Some a
                  | S p => LNth p l'
                  end
  end.


(** Exercise 13.2 *)

Definition is_LLeaf (A : Set) (t : LTree A) : Prop := 
  match t with
    | LLeaf => True
    | _ => False
  end.

Definition L_root (A : Set) (t : LTree A) := 
  match t with
    | LLeaf => False
    | LBin _ _ _ => True
  end.

Definition L_left_son (A : Set) (t : LTree A) : option (LTree A) :=
  match t with
    | LLeaf => None
    | LBin a l r => Some l
  end. 

Definition L_right_son (A : Set) (t : LTree A) : option (LTree A) :=
  match t with
    | LLeaf => None
    | LBin a l r => Some r
  end. 

Inductive direction: Set := d0 (* left *) | d1 (* right *).
Definition path : Set := list direction.

Fixpoint L_subtree (A : Set) (t : LTree A) (p : path) : option (LTree A) :=
  match p with
    | nil => Some t
    | cons d p' => 
      match t with
        | LLeaf => None
        | LBin a l r => 
            match d with
              | d0 => (L_subtree l p')
              | d1 => (L_subtree r p')
            end
      end
  end.

Fixpoint Ltree_label (A:Set)(t:LTree A)(p:path) : option A :=
  match p with
    | nil => match t with
              | LLeaf => None
              | LBin a l r => Some a
            end
    | cons d p' => match t with
                    | LLeaf => None
                    | LBin a l r => 
                        match d with
                          | d0 => Ltree_label l p'
                          | d1 => Ltree_label r p'
                        end
                  end
  end.

(** []*)


CoFixpoint from (n:nat) : LList nat := LCons n (from (S n)).

Definition Nats : LList nat := from 0.

CoFixpoint omega_repeat (A:Set) (a:A) : LList A := LCons a (omega_repeat a).

CoFixpoint LAppend (A:Set) (u v:LList A) : LList A :=
  match u with
  | LNil => v
  | LCons a u' => LCons a (LAppend u' v)
  end.

CoFixpoint general_omega (A:Set) (u v:LList A) : LList A :=
  match v with
  | LNil => u
  | LCons b v' =>
      match u with
      | LNil => LCons b (general_omega v' (LCons b v'))
      | LCons a u' => LCons a (general_omega u' (LCons b v'))
      end
  end.

Definition omega (A:Set) (u:LList A) : LList A := general_omega u u.


(** Exercise 13.3 *)

Require Import ZArith.

CoFixpoint pfrom (p : positive) : LTree positive :=
  LBin p (pfrom (xO p)) (pfrom (xI p)).

Definition Pos := pfrom xH.

(** [] *)


(** Exercise 13.3 *)

CoFixpoint graft (A:Set)(t t':LTree A) : LTree A :=
  match t with
    | LLeaf => t'
    | LBin a l r => LBin a (graft l t') (graft r t')
  end. 

(** [] *)


(** Exercise 13.4 *)

CoFixpoint LMap (A B : Set)(f : A -> B)(l : LList A) : LList B :=
  match l with
    | LNil => LNil
    | LCons h t => LCons (f h) (LMap f t)
  end. 
  
(** [] *)


Definition LList_decomp (A:Set) (l:LList A) : LList A :=
  match l with
  | LNil => LNil
  | LCons a l' => LCons a l'
  end.

Lemma LList_decompose : forall (A:Set) (l:LList A), l = LList_decomp l.
Proof.
 intros A l; case l; trivial.
Qed.


(** Exercise 13.6 *)

Definition LTree_decomp (A:Set)(t:LTree A) : LTree A := 
  match t with
    | LLeaf => LLeaf
    | LBin x l r => LBin x l r
  end.

Lemma LTree_decompose : forall (A:Set)(t:LTree A),
  LTree_decomp t = t. 
Proof. 
  intros A t. 
  destruct t; trivial. 
Qed. 

(** [] *)


(** Exercise 13.7 *)

Fixpoint LList_decomp_n (A:Set)(n:nat)(l:LList A) : LList A :=  
  match n with
    | 0 => l
    | S p => match  l with
              | LNil => LNil
              | LCons h t => LCons h (LList_decomp_n p t)
            end
  end. 

Theorem LList_decompose_n : forall (A:Set)(l:LList A)(n:nat), 
  l = LList_decomp_n n l.
Proof. 
  intros A l n. 
  generalize dependent l.
  induction n as [|n']. 
  - trivial. 
  - intros l. destruct l. 
    + trivial. 
    + simpl. rewrite <- IHn'. 
      reflexivity. 
Qed. 

(** [] *)


Definition Squares_from :=
  let sqr := fun n:nat => n * n in
  (cofix F : nat -> LList nat := fun n:nat => LCons (sqr n) (F (S n))).

Require Import List.

Eval simpl in ((1 :: 2 :: nil) ++ 3 :: 4 :: nil).

Eval simpl in
  (LAppend (LCons 1 (LCons 2 LNil)) (LCons 3 (LCons 4 LNil))).


Lemma LAppend_one :
 forall (A:Set) (a:A) (u v:LList A),
   LAppend (LCons a u) v = LCons a (LAppend u v).
Proof.
 simpl in |- *.
Abort.

Eval simpl in
  (LList_decomp
     (LAppend (LCons 1 (LCons 2 LNil)) (LCons 3 (LCons 4 LNil )))).


Ltac LList_unfold term := apply trans_equal with (1 := LList_decompose term).

Lemma LAppend_LNil : forall (A:Set) (v:LList A), LAppend LNil v = v.
Proof.
 intros A v.
 LList_unfold (LAppend LNil v). 
 case v; simpl in |- *; auto.
Qed.

Lemma LAppend_LCons :
  forall (A:Set) (a:A) (u v:LList A),
    LAppend (LCons a u) v = LCons a (LAppend u v).
Proof.
 intros A a u v.
 LList_unfold (LAppend (LCons a u) v).
 case v; simpl in |- *; auto.
Qed.
 
Hint Rewrite  LAppend_LNil LAppend_LCons : llists.


(** Exercise 13.8 *)

Lemma from_unfold : forall n:nat, from n = LCons n (from (S n)).
Proof. 
  intros n. 
  LList_unfold (from n). destruct n; reflexivity. 
Qed. 

Lemma omega_repeat_unfold : forall (A:Set) (a:A), 
  omega_repeat a = LCons a (omega_repeat a).
Proof. 
  intros A a.
  LList_unfold (omega_repeat a). 
  trivial. 
Qed. 

Lemma general_omega_LNil : forall A : Set, omega LNil = LNil (A:=A). 
Proof. 
  intros A. LList_unfold (@omega A LNil). trivial. 
Qed. 

Lemma general_omega_LCons : forall (A : Set) (a : A) (u v : LList A),
  general_omega (LCons a u) v = LCons a (general_omega u v). 
Proof. 
  intros A a u v.
  LList_unfold (general_omega (LCons a u) v). 
  destruct v. 
  - simpl. 
    cut (general_omega u LNil = u). 
    + intros H. rewrite H. reflexivity. 
    + LList_unfold (general_omega u LNil). 
      destruct u; trivial. 
  - trivial. 
Qed.

Lemma general_omega_LNil_LCons :
  forall (A : Set) (a : A) (u : LList A),
   general_omega LNil (LCons a u) = LCons a (general_omega u (LCons a u)). 
Proof. 
  intros A a u.
  LList_unfold (general_omega LNil (LCons a u)). trivial. 
Qed.

Lemma general_omega_shoots_again : forall (A:Set) (v:LList A),
  general_omega LNil v = general_omega v v. 
Proof. 
  intros A v. 
  LList_unfold (general_omega LNil v). 
  destruct v. 
  - simpl. symmetry. 
    LList_unfold (@general_omega A LNil LNil). trivial. 
  - simpl. symmetry. 
    LList_unfold (general_omega (LCons a v) (LCons a v)). trivial. 
Qed. 

Hint Rewrite general_omega_LNil 
             general_omega_LCons
             general_omega_LNil_LCons
             general_omega_shoots_again : llists. 
    
(** [] *)


(** Exercise 13.9 *)

Ltac LTree_unfold term :=
  replace term with (LTree_decomp term); try apply LTree_decompose.

Lemma graft_LNil : forall (A : Set) (t : LTree A),
  graft LLeaf  t = t. 
Proof. 
  intros A t. 
  eapply eq_trans. 
  - symmetry. apply (LTree_decompose (graft LLeaf t)). 
  - destruct t; trivial. 
Qed. 

(** [] *)


Inductive Finite (A:Set) : LList A -> Prop :=
  | Finite_LNil : Finite LNil
  | Finite_LCons : forall (a:A) (l:LList A), Finite l -> Finite (LCons a l).

Hint Resolve Finite_LNil Finite_LCons: llists.

Remark one_two_three : Finite (LCons 1 (LCons 2 (LCons 3 LNil))).
Proof.
 auto with llists.
Qed.

Theorem Finite_of_LCons :
 forall (A:Set) (a:A) (l:LList A), Finite (LCons a l) -> Finite l.
Proof.
 intros A a l H; inversion H; assumption.
Qed.

Theorem LAppend_of_Finite :
 forall (A:Set) (l l':LList A),
   Finite l -> Finite l' -> Finite (LAppend l l').
Proof.
 intros A l l' H.
 induction H; autorewrite with llists  using auto with llists.
Qed.


(** Exercise 13.10 *)

Ltac LList_unfold_l :=
  match goal with
    | [ |- ?X1 = _] => LList_unfold X1
  end.


Lemma omega_general : forall (A : Set) (u : LList A),
  omega u = general_omega u u. 
Proof.
  intros A u. unfold omega. reflexivity. 
Qed.


Lemma general_omega_of_Finite : forall (A:Set) (u:LList A),
   Finite u ->
   forall v:LList A, general_omega u v = LAppend u (general_omega v v).
Proof.
  intros A u H v. induction H. 
  - rewrite LAppend_LNil.
    exact (general_omega_shoots_again v). 
  - rewrite general_omega_LCons. 
    autorewrite with llists. 
    rewrite <- IHFinite. reflexivity. 
Qed. 

Theorem omega_of_Finite : forall (A : Set) (u : LList A),
  Finite u -> omega u = LAppend u (omega u). 
Proof.
  intros A u H. unfold omega. 
  apply (general_omega_of_Finite  H u). 
Qed. 

(** [] *)


(** Exercise 13.11 *)

Inductive Finite_LTree (A : Set) : LTree A -> Prop := 
  | Finite_LLeaf : Finite_LTree LLeaf
  | Finite_LBin : forall (a : A)(l r : LTree A), 
                    Finite_LTree l -> Finite_LTree r -> Finite_LTree (LBin a l r). 

Theorem graft_of_Finite : forall (A : Set) (t : LTree A),
  Finite_LTree t -> graft t LLeaf = t. 
Proof. 
  intros A t H. 
  induction H. 
  - apply graft_LNil. 
  - match goal with
      | [ |- ?t = _] => replace t with (LTree_decomp t)
    end. 
    + simpl. rewrite IHFinite_LTree1. rewrite IHFinite_LTree2. reflexivity. 
    + apply LTree_decompose. 
Qed.  

(** *)



CoInductive Infinite (A:Set) : LList A -> Prop :=
    Infinite_LCons :
      forall (a:A) (l:LList A), Infinite l -> Infinite (LCons a l).

Hint Resolve Infinite_LCons: llists.

(* manual proof (look at from_Infinite) *)
Definition F_from :
  (forall n:nat, Infinite (from n)) -> forall n:nat, Infinite (from n).
 intros H n. rewrite (from_unfold n). 
 split.
 auto.
Defined.

Print F_from.


Theorem from_Infinite_V0 : forall n:nat, Infinite (from n).
Proof (cofix H : forall n:nat, Infinite (from n) := F_from H).

(* end of manual proof *)

(* direct  proof *)
Lemma from_Infinite : forall n:nat, Infinite (from n).
Proof.
 cofix H.
 intro n; rewrite (from_unfold n).
 split; auto.
Qed.

Print from_Infinite.

Lemma from_Infinite_buggy : forall n:nat, Infinite (from n).
Proof.
 cofix H.
 auto with llists.
Abort.


(** Exercise 13.12 *)

Lemma repeat_infinite : forall (A:Set) (a:A), Infinite (omega_repeat a).
Proof. 
  cofix H. 
  intros A a. rewrite omega_repeat_unfold. 
  split. auto. 
Qed. 

Lemma general_omega_infinite : forall (A : Set) (a : A) (u v : LList A),
  Infinite (general_omega v (LCons a u)). 
Proof. 
  cofix H. intros A a u v. 
  destruct v. 
  - rewrite general_omega_LNil_LCons. 
    split. auto. 
  - match goal with
      | [ |- Infinite ?t] => replace t with (LList_decomp t)
    end. 
    + simpl. split. auto. 
    + rewrite LList_decompose; reflexivity. 
Qed. 

Theorem omega_infinite : forall (A : Set) (a : A) (l : LList A),
  Infinite (omega (LCons a l)). 
Proof. 
  intros A a l. 
  rewrite omega_general. 
  apply general_omega_infinite. 
Qed. 

(** [] *)


(** Exercise 13.13 *)

Inductive BugInfinite (A : Set) : LList A -> Prop := 
  BugInfinite_intro : forall (a : A)(l : LList A),
    BugInfinite l -> BugInfinite (LCons a l). 

Theorem BugInfinite_False : forall (A : Set)(l : LList A), ~BugInfinite l.
Proof. 
  
Admitted.  

(** [] *)


(** Exercise 13.14 *)

CoInductive ExistBranchInfinite (A : Set) : LTree A -> Prop :=
  | EBI_intro_l : forall a l r, ExistBranchInfinite l -> ExistBranchInfinite (LBin a l r)
  | EBI_intro_r : forall a l r, ExistBranchInfinite r -> ExistBranchInfinite (LBin a l r).

CoInductive AllBranchInfinite (A : Set) : LTree A -> Prop :=
  | ABI_intro : forall a l r, AllBranchInfinite l -> AllBranchInfinite r ->
                         AllBranchInfinite (LBin a l r).

Inductive ExistBranchFinite (A : Set) : LTree A -> Prop := 
  | EBF_Leaf : ExistBranchFinite LLeaf
  | EBF_Bin_l : forall a l r, ExistBranchFinite l -> ExistBranchFinite (LBin a l r)
  | EBF_Bin_r : forall a l r, ExistBranchFinite r -> ExistBranchFinite (LBin a l r).

Inductive AllBranchFinite (A : Set) : LTree A -> Prop := 
  | ABF_Leaf : AllBranchFinite LLeaf
  | ABF_Bin  : forall a l r, AllBranchFinite l -> AllBranchFinite r ->
                        AllBranchFinite (LBin a l r). 

CoFixpoint treeall (n : nat) : LTree nat := 
  LBin n (treeall n) (treeall n).

Example ABI_Example : AllBranchInfinite (treeall 0).
Proof.
  cofix H. 
  match goal with
    | [  |- AllBranchInfinite ?t ] => LTree_unfold t
  end.
  - simpl. split; auto.
Qed.

Example EBI_Example : ExistBranchInfinite (LBin 0 LLeaf (treeall 0)).
Proof.
  apply EBI_intro_r.
  cofix H.
  match goal with
    | [  |- ExistBranchInfinite ?t ] => LTree_unfold t
  end.
  - simpl. constructor; auto.
Qed.

Axiom class : forall P:Prop , ~~P -> P.

Theorem NEBF_EBI : forall (A : Set)(t : LTree A),
  ~ ExistBranchFinite t -> ExistBranchInfinite t.
Proof.

Admitted.  

(** [] *)



Lemma LNil_not_Infinite : forall A:Set, ~ Infinite (LNil (A:=A)).
Proof.
 intros A H;  inversion H. 
Qed.


(** Exercise 13.15 *)

Lemma Infinite_of_LCons :  forall (A:Set) (a:A) (u:LList A), Infinite (LCons a u) -> Infinite u.
Proof.
  intros A a u H. inversion H. assumption.
Qed.
 
Lemma LAppend_of_Infinite : forall (A:Set) (u:LList A),
    Infinite u -> forall v:LList A, Infinite (LAppend u v).
Proof.
  cofix H0.
  intros A u H v. 
  inversion H. 
  rewrite LAppend_LCons. 
  constructor. 
  apply H0. assumption.
Qed.

Lemma Finite_not_Infinite :
 forall (A:Set) (l:LList A), Finite l -> ~ Infinite l.
Proof.
  intros A l F I.
  induction F. 
  - inversion I. 
  - inversion I. apply (IHF H0).
Qed.

Lemma Infinite_not_Finite :
  forall (A:Set) (l:LList A), Infinite l -> ~ Finite l.
Proof.
  intros A l H F. 
  induction F. 
  - inversion H. 
  - apply IHF. inversion H. assumption.
Qed.

Lemma Not_Finite_Infinite :
  forall (A:Set) (l:LList A), ~ Finite l -> Infinite l.
Proof.
  cofix H. 
  intros A l H0. destruct l. 
  - elim H0. constructor.
  - split. apply H. 
    intros H1. apply H0. constructor; assumption.
Qed.

(** [] *)


(** Exercise 13.16 *)

Require Import Classical.

Lemma Not_Infinite_Finite : forall (A : Set)(l : LList A),
  ~ Infinite l -> Finite l.
Proof.
  intros A l H. apply NNPP.
  intros NF. apply H. apply Not_Finite_Infinite. assumption.
Qed.

Lemma Finite_or_Infinite : forall (A : Set)(l : LList A),
  Finite l \/ Infinite l.
Proof.
  intros A l.
  destruct (classic (Finite l)). 
  - left; assumption.
  - right; apply Not_Finite_Infinite; assumption.
Qed.

(** [] *)

(** Exercise 13.17 *)

Definition Infinite_ok (A:Set) (X:LList A -> Prop) :=
  forall l:LList A,  X l -> 
  exists a : A, ( exists l' : LList A, l = LCons a l' /\ X l').
 
Definition Infinite1 (A:Set) (l:LList A) :=
   exists X : LList A -> Prop , Infinite_ok X /\ X l.


Lemma Inf_ok : forall (A : Set), @Infinite_ok A (@Infinite A).
Proof.
  unfold Infinite_ok. intros A l H.
  inversion H. exists a. exists l0. 
  split; trivial.
Qed.

Lemma Inf_Inf1 : forall (A : Set)(l : LList A),
  Infinite l -> Infinite1 l. 
Proof.
  intros A l H.
  unfold Infinite1. 
  exists (@Infinite A). split.
  - apply Inf_ok.
  - assumption.
Qed.

Lemma Inf1_Cons : forall (A : Set)(a : A)(l : LList A),
  Infinite1 (LCons a l) -> Infinite1 l.
Proof.
  intros A a l H.
  unfold Infinite1 in H. destruct H as [X [H0 H1]]. 
  unfold Infinite_ok in H0. 
  destruct (H0 (LCons a l) H1) as [a' [l' [H2 H3]]]. 
  unfold Infinite1. exists X. split.
  - unfold Infinite_ok. assumption. 
  - inversion H2. assumption. 
Qed.
  

Lemma Inf1_Inf : forall (A : Set)(l : LList A),
  Infinite1 l -> Infinite l.
Proof.
  cofix H. intros A l H0.
  destruct l. 
  - unfold Infinite1 in H0. 
    unfold Infinite_ok in H0. 
    destruct H0 as [X [H1 H2]].
    destruct (H1 LNil H2) as [a [l' [H3 H4]]]. 
    inversion H3. 
  - constructor. apply (H A l (Inf1_Cons H0)).
Qed.  
  
(** [] *)


Lemma Lappend_of_Infinite_0 :
 forall (A:Set) (u:LList A), Infinite u -> forall v:LList A, u = LAppend u v.
Proof.
 simple destruct u.
 intro H; inversion H.
 intros a l H; inversion H; intros.
 rewrite LAppend_LCons.
 cut (l = LAppend l v).
 simple induction 1; auto.
Abort.


CoInductive bisimilar (A:Set) : LList A -> LList A -> Prop :=
  | bisim0 : bisimilar LNil LNil
  | bisim1 :
      forall (a:A) (l l':LList A),
        bisimilar l l' -> bisimilar (LCons a l) (LCons a l').

 Hint Resolve bisim0 bisim1: llists.



(** Exercise 13.19 *)

Require Import Relations.

Lemma bisimilar_refl : forall A:Set, reflexive _ (@bisimilar A).
Proof.
  intros A. unfold reflexive. 
  cofix H. intros x. destruct x. 
    + apply bisim0. 
    + constructor. apply H. 
Qed.

Lemma bisimilar_trans : forall A : Set, transitive (LList A) (@bisimilar A).
Proof.
  intro A. unfold transitive. 
  cofix. intros x y z Hxy Hyz.
  inversion Hxy. 
  + inversion Hyz. 
    * constructor. 
    * rewrite <- H0 in H2. inversion H2. 
  + inversion Hyz. 
    * rewrite <- H2 in H1. inversion H1. 
    * rewrite <- H1 in H3. 
      injection H3. intros H5 H6. rewrite H6.
      constructor. rewrite H5 in H2.
      apply bisimilar_trans with (y:=l'); assumption. 
Qed.

Lemma bisimilar_sym : forall A : Set, symmetric (LList A) (@bisimilar A).
Proof. 
  intros A. unfold symmetric. 
    cofix H. intros x y H0.
    inversion H0. 
    + constructor. 
    + constructor. apply H; assumption.
Qed.


Theorem bisimilar_equiv : forall (A:Set), equiv (LList A) (@bisimilar  A).
Proof.
  intros A. unfold equiv. repeat split. 
  apply bisimilar_refl. 
  apply bisimilar_trans. 
  apply bisimilar_sym.
Qed.

(** [] *)


(** Exercise 13.20 *)

Lemma bisimilar_LNth :
 forall (A:Set) (n:nat) (u v:LList A), bisimilar u v -> LNth n u = LNth n v.
Proof.
  intros A n. 
  induction n; intros u v H. 
  - inversion H; reflexivity. 
  - inversion H. 
    + reflexivity. 
    + simpl. apply IHn. assumption. 
Qed.

Lemma LNth_bisimilar : forall (A:Set) (u v:LList A),
   (forall n:nat, LNth n u = LNth n v) -> bisimilar u v.
Proof.
  cofix H.
  intros A u v H0.
  destruct  u. 
  - destruct v. 
    + constructor. 
    + discriminate (H0 0).
  - destruct v. 
    + discriminate (H0 0).
    + injection (H0 0). intros H1. 
      rewrite <- H1. constructor. 
      apply H. intros n.  apply (H0 (S n)).
Qed.

(** [] *)


(** Exercise 13.21 *)

Theorem bisimilar_of_Finite_is_Finite :
 forall (A:Set) (l:LList A),
   Finite l -> forall l':LList A, bisimilar l l' -> Finite l'.
Proof.
  intros A l F.
  induction F; intros l' B.
  - inversion B. constructor. 
  - inversion B. constructor. 
    apply (IHF l'0); assumption. 
Qed.

Theorem bisimilar_of_Infinite_is_Infinite :
 forall (A:Set) (l:LList A),
   Infinite l -> forall l':LList A, bisimilar l l' -> Infinite l'.
Proof.
  cofix H. 
  intros A l Inf. intros l' B. 
  inversion B. 
  - rewrite <- H0 in Inf. inversion Inf. 
  - constructor. apply (H A l0). 
    + inversion Inf. rewrite <- H1 in H4. 
      injection H4. intros H5 H6. 
      rewrite <- H5. assumption. 
    + assumption. 
Qed.

(** [] *)


(** Exercise 13.22 *)

Theorem bisimilar_of_Finite_is_eq : forall (A:Set) (l:LList A),
   Finite l -> forall l':LList A, bisimilar l l' -> l = l'.
Proof.
  intros A l F. 
  induction F; intros l' B. 
  - inversion B. trivial. 
  - inversion B. cut (l = l'0). 
    + intros H3. rewrite H3. reflexivity. 
    + apply IHF. assumption. 
Qed.

(** [] *)


(** Exercise 13.23 *)

CoInductive LTree_bisimilar (A : Set) : LTree A -> LTree A -> Prop :=
  | bismt0 : LTree_bisimilar LLeaf LLeaf 
  | bismt1 : forall a l1 r1 l2 r2, LTree_bisimilar l1 l2 -> LTree_bisimilar r1 r2 ->
                              LTree_bisimilar (LBin a l1 r1) (LBin a l2 r2).

Fixpoint LPth (A : Set) (p : positive) (t : LTree A) {struct p} : option A :=
  match t with
    | LLeaf => None
    | LBin a l r => match p with
                     | xH => Some a
                     | xO p' => LPth p' l
                     | xI p' => LPth p' r
                   end
  end. 

Lemma bisimilar_LPth : forall (A : Set) (p : positive) (t s : LTree A),
  LTree_bisimilar t s -> LPth p t = LPth p s.
Proof.
  intros A p.
  induction p; intros t s H.
  - destruct t; destruct s; try (inversion H; trivial).
    simpl. apply IHp. assumption. 
  - destruct t; destruct s; try (inversion H; trivial).
    simpl. apply IHp. assumption.
  - destruct t; destruct s; try (inversion H; trivial). 
Qed.    

Lemma LPth_bisimilar : forall (A : Set)(t s : LTree A),
  (forall p : positive, LPth p t = LPth p s) -> LTree_bisimilar t s. 
Proof. 
  cofix H. intros A t s H0. 
  destruct t; destruct s. 
  - constructor. 
  - discriminate (H0 1%positive). 
  - discriminate (H0 1%positive). 
  - injection (H0 1%positive). intros H1.
    rewrite <- H1. 
    constructor. 
    + apply H. intros p. apply (H0 (xO p)).
    + apply H. intros p. apply (H0 (xI p)). 
Qed.

(** [] *)


Lemma LAppend_assoc :
 forall (A:Set) (u v w:LList A),
   bisimilar (LAppend u (LAppend v w)) (LAppend (LAppend u v) w).
Proof.
 intro A; cofix H.
 simple destruct u; intros; autorewrite with llists using auto with llists.
 apply bisimilar_refl.
Qed.


(** Exercise 13.24 *)

Lemma LAppend_of_Infinite_bisim : forall (A:Set) (u:LList A),
    Infinite u -> forall v:LList A, bisimilar u (LAppend u v).
Proof.
  intro A. cofix H.
  intros u H0 v. inversion H0. 
  rewrite LAppend_LCons. constructor. 
  apply H. assumption. 
Qed.

(** [] *)


(** Exercise 13.25 *)

Lemma eq_bisimilar : forall (A : Set) (u v : LList A),
  u = v -> bisimilar u v. 
Proof. 
  intros A. cofix H. 
  intros u v E. 
  destruct u; destruct v. 
  - constructor.
  - inversion E. 
  - inversion E. 
  - inversion E. rewrite <- H1. 
    constructor. apply H. reflexivity. 
Qed. 
 
Lemma general_omega_lappend : forall (A:Set) (u v: LList A),
    bisimilar (general_omega v u) (LAppend v (omega u)).
Proof.
  intro A. cofix H. 
  intros u v. destruct v. 
  - destruct u. 
    + rewrite <- omega_general. 
      rewrite general_omega_LNil. 
      rewrite LAppend_LNil. constructor. 
    + rewrite general_omega_LNil_LCons. 
      unfold omega. rewrite LAppend_LNil. 
      rewrite general_omega_LCons. 
      constructor. apply eq_bisimilar. reflexivity. 
  - destruct u. 
    + rewrite general_omega_LCons. 
      rewrite LAppend_LCons. constructor. apply H. 
    + autorewrite with llists. constructor. apply H. 
Qed.

Lemma omega_lappend :
 forall (A:Set) (u:LList A), bisimilar (omega u) (LAppend u (omega u)).
Proof.
  intros A u. unfold omega. apply general_omega_lappend. 
Qed.

(** [] *)


(** Exercise 13.26 *)

Lemma graft_of_Infinite_bisim : forall (A : Set)(t t' : LTree A),
  AllBranchInfinite t -> LTree_bisimilar t (graft t t'). 
Proof. 
  intros A. cofix H. 
  intros t t' H0. inversion H0. 
  match goal with
    | [ |- _ _ ?t ] => LTree_unfold t
  end. simpl. 
  constructor; apply H; assumption. 
Qed.
  
(** [] *)


Definition bisimulation (A:Set) (R:LList A -> LList A -> Prop) :=
  forall l1 l2:LList A,
     R l1 l2 ->
     match l1 with
     | LNil => l2 = LNil
     | LCons a l'1 =>
         match l2 with
         | LNil => False
         | LCons b l'2 => a = b /\ R l'1 l'2
         end
     end.


(** Exercise 13.27 *) 

Theorem park_principle : forall (A:Set) (R:LList A -> LList A -> Prop),
    bisimulation R -> forall l1 l2:LList A, R l1 l2 -> bisimilar l1 l2. 
Proof.
  intros A R B. unfold bisimulation in B. 
  cofix H. intros l1 l2 H0.
  destruct l1. 
  - destruct l2. 
    + constructor. 
    + discriminate (B LNil (LCons a l2) H0). 
  - destruct l2. 
    + elim (B (LCons a l1) LNil H0).
    + destruct (B (LCons a l1) (LCons a0 l2) H0) as [E H1]. 
      rewrite <- E. constructor. apply H. assumption. 
Qed.

(** [] *)


(** Exercise 13.28 *) 

CoFixpoint alter  : LList bool := LCons true (LCons false alter).

Definition alter2 : LList bool := omega (LCons true (LCons false LNil)).

Definition R (l1 l2:LList bool) : Prop :=
  l1 = alter /\ l2 = alter2 \/
  l1 = LCons false alter /\ l2 = LCons false alter2.


Lemma R_bisim : bisimulation R.
Proof.
  unfold bisimulation. 
  intros l1 l2 H. unfold R in H. 
  destruct H as [[H0 H1]| [H0 H1]]. 
  - rewrite H0; rewrite H1. simpl. 
    split. reflexivity. 
    rewrite general_omega_LCons. 
    rewrite general_omega_shoots_again. 
    rewrite <- omega_general. fold alter2. 
    right. auto. 
  - rewrite H0; rewrite H1. 
    split; [reflexivity | left; auto].
Qed.

(** [] *)


(* LTL operators *)
 
Section LTL.
Variables (A : Set) (a b c : A).


Definition satisfies (l:LList A) (P:LList A -> Prop) : Prop := P l.
Hint Unfold satisfies: llists.

 Inductive Atomic (At:A -> Prop) : LList A -> Prop :=
     Atomic_intro : forall (a:A) (l:LList A), At a -> Atomic At (LCons a l).

 Hint Resolve Atomic_intro: llists.

 Inductive Next (P:LList A -> Prop) : LList A -> Prop :=
     Next_intro : forall (a:A) (l:LList A), P l -> Next P (LCons a l).

 Hint Resolve Next_intro: llists.

 Lemma Next_example : satisfies (LCons a (omega_repeat b)) (Next (Atomic (eq b))).
 Proof.
   rewrite (omega_repeat_unfold b); auto with llists. 
 Qed.


   
  
 Inductive Eventually (P:LList A -> Prop) : LList A -> Prop :=
   | Eventually_here :
       forall (a:A) (l:LList A), P (LCons a l) -> Eventually P (LCons a l)
   | Eventually_further :
       forall (a:A) (l:LList A), Eventually P l -> Eventually P (LCons a l).

 Hint Resolve Eventually_here Eventually_further: llists.


 Lemma Eventually_of_LAppend :
  forall (P:LList A -> Prop) (u v:LList A),
    Finite u ->
    satisfies v (Eventually P) -> satisfies (LAppend u v) (Eventually P).
 Proof.                       
  unfold satisfies in |- *; simple induction 1; intros;
   autorewrite with llists  using auto with llists.
 Qed.

 CoInductive Always (P:LList A -> Prop) : LList A -> Prop :=
    Always_LCons :
        forall (a:A) (l:LList A),
          P (LCons a l) -> Always P l -> Always P (LCons a l).

  
 Hint Resolve Always_LCons: llists.

 Lemma Always_Infinite :
   forall (P:LList A -> Prop) (l:LList A),
     satisfies l (Always P) -> Infinite l.
 Proof.
  intro P; cofix H.
  simple destruct l. 
  intro H0; inversion H0.
  intros a0 l0 H0; split.
  apply H; auto.
  inversion H0; auto.
 Qed.


 Definition F_Infinite (P:LList A -> Prop) : LList A -> Prop :=
   Always (Eventually P).

  Definition F_Infinite_2_Eventually : forall P l, F_Infinite P l-> Eventually P l.
 intros P l. 
  case l.
  inversion 1.
  inversion 1.
   assumption.
 Defined.

Section A_Proof_with_F_Infinite.
   
   Let w : LList A := LCons a (LCons b LNil).

   Let w_omega := omega w.

   Let P (l:LList A) : Prop := l = w_omega \/ l = LCons b w_omega.


  Remark P_F_Infinite :
   forall l:LList A, P l -> satisfies l (F_Infinite (Atomic (eq a))).
  Proof.
   unfold F_Infinite in |- *.
   cofix.
   intro l; simple destruct 1.
   intro eg; rewrite eg.
   unfold w_omega in |- *; rewrite omega_of_Finite.
   unfold w in |- *.
   autorewrite with llists  using auto with llists.
   split.
   auto with llists.
   apply P_F_Infinite.
   unfold P in |- *; auto.
   unfold w in |- *; auto with llists.
   intro eg; rewrite eg.
   unfold w_omega in |- *; rewrite omega_of_Finite.
   unfold w in |- *.
   rewrite LAppend_LCons.
   split.
   auto with llists.
   apply P_F_Infinite.
   unfold P in |- *; left.
   rewrite <- LAppend_LCons.
   rewrite <- omega_of_Finite.
   trivial.
   auto with llists.
   unfold w in |- *; auto with llists.
  Qed.

  Lemma omega_F_Infinite : satisfies w_omega (F_Infinite (Atomic (eq a))).
  Proof.
   apply P_F_Infinite.
   unfold P in |- *; left.
   trivial.
  Qed.
 
 End A_Proof_with_F_Infinite.

 Theorem F_Infinite_cons :
  forall (P:LList A -> Prop) (a:A) (l:LList A),
    satisfies l (F_Infinite P) -> satisfies (LCons a l) (F_Infinite P).
 Proof.
  split.
  inversion H.
  right.
  auto.
  assumption.
 Qed.

 Theorem F_Infinite_consR :
 forall (P:LList A -> Prop) (a:A) (l:LList A),
   satisfies (LCons a l) (F_Infinite P) -> satisfies l (F_Infinite P).
 Proof.
  inversion 1.
  assumption.
 Qed.

 Definition G_Infinite (P:LList A -> Prop) : LList A -> Prop :=
   Eventually (Always P).

 Lemma always_a : satisfies (omega_repeat a) (Always (Atomic (eq a))).
 Proof.
  unfold satisfies in |- *; cofix H.
  rewrite (omega_repeat_unfold a).
  auto with llists.
 Qed.

 Lemma LAppend_G_Infinite :
  forall (u v:LList A) (P:LList A -> Prop),
    Finite u ->
    satisfies v (G_Infinite P) -> 
    satisfies (LAppend u v) (G_Infinite P).
 Proof.
  simple induction 1.
  autorewrite with llists  using auto.
  intros; autorewrite with llists  using auto.
  unfold G_Infinite in |- *; auto with llists.
  right.
  apply H1.
  auto.
 Qed.

 Lemma LAppend_G_Infinite_R :
  forall (u v:LList A) (P:LList A -> Prop),
    Finite u ->
    satisfies (LAppend u v) (G_Infinite P) -> 
    satisfies v (G_Infinite P).
 Proof.
  simple induction 1.
  autorewrite with llists  using auto.
  intros; autorewrite with llists using auto.
  rewrite LAppend_LCons in H2.
  inversion_clear H2.
  apply H1.
  inversion_clear H3.
  generalize H4; case (LAppend l v).
  intro H5; inversion H5.  
  left.
  auto.
  auto.
 Qed.

End LTL.

Hint Unfold satisfies: llists.
Hint Resolve Always_LCons: llists.
Hint Resolve Eventually_here Eventually_further: llists.
Hint Resolve Next_intro: llists.
Hint Resolve Atomic_intro: llists.

(* Automata *)

Record automaton : Type := mk_auto
  {states : Set;
   actions : Set;
   initial : states;
   transitions : states -> actions -> list states}.

Hint Unfold transitions: automata.

Definition deadlock (A:automaton) (q:states A) :=
  forall a:actions A, @transitions A q a = nil.



Unset Implicit Arguments.
Set Strict Implicit.
CoInductive Trace (A:automaton) : states A -> LList (actions A) -> Prop :=
  | empty_trace : forall q:states A, deadlock A q -> Trace A q LNil 
  | lcons_trace :
      forall (q q':states A) (a:actions A) (l:LList (actions A)),
        In q' (transitions A q a) -> Trace A q' l -> Trace A q (LCons a l).
Set Implicit Arguments.
Unset Strict Implicit.


Section exemple.

(* states *)
Inductive st : Set :=
  | q0 : st
  | q1 : st
  | q2 : st.

(* actions *)
Inductive acts : Set :=
  | a : acts
  | b : acts.


(* transitions *)
Definition trans (q:st) (x:acts) : list st :=
  match q, x with
  | q0, a => q1 :: nil
  | q0, b => q1 :: nil
  | q1, a => q2 :: nil
  | q2, b => q2 :: q1 :: nil
  | _, _ => nil
  end.

(* a toy automaton *)
Definition A1 := mk_auto q0 trans.
      
Hint Unfold A1.

Lemma no_deadlocks : forall q:states A1, ~ deadlock  A1 q.
Proof.
 unfold deadlock in |- *; simple destruct q; intro H.
 absurd (transitions A1 q0 a = nil). 
 simpl in |- *; discriminate.
 auto.
 absurd (transitions A1 q1 a = nil). 
 simpl in |- *; discriminate.
 auto.
 absurd (transitions A1 q2 b = nil). 
 simpl in |- *; discriminate.
 auto.
Qed.

Lemma from_q1 :
 forall t:LList acts,
   Trace A1 q1 t ->
    exists t' : LList acts, Trace A1 q2 t' /\ t = LCons a t'.
Proof.
 intros t H; inversion_clear H.
 case (no_deadlocks H0). 
 generalize H0 H1; case a0; simpl in |- *.
 do 2 simple destruct 1.
 exists l; auto.
 contradiction. 
Qed.



Lemma from_q0 :
 forall t:LList acts,
   Trace A1 q0 t ->
    exists t' : LList acts,
     Trace A1 q2 t' /\ (t = LCons a (LCons a t') \/ t = LCons b (LCons a t')).
Proof.
 intros t H; inversion_clear H.
 case (no_deadlocks H0). 
 generalize H0 H1; case a0; simpl in |- *.
 do 2 simple destruct 1.
 intro H3; case (from_q1 H3).
 intros x [H4 H5].
 exists x; auto.
 rewrite H5; auto.
 do 2 simple destruct 1.
 intro H3; case (from_q1 H3).
 intros x [H4 H5].
 exists x; auto.
 rewrite H5; auto.
Qed.

Lemma from_q2 :
 forall t:LList acts,
   Trace A1 q2 t ->
    exists t' : LList acts,
     (Trace A1 q2 t' \/ Trace A1 q1 t') /\ t = LCons b t'.
Proof.
 intros t H; inversion_clear H.
 case (no_deadlocks H0).  
 generalize H0 H1; case a0; simpl in |- *.
 contradiction.
 do 2 simple destruct 1.
 exists l; auto.
 exists l; auto.
 rewrite H3; auto.
 contradiction.
Qed.

Theorem Infinite_bs :
 forall (q:states A1) (t:LList acts),
   Trace A1 q t -> satisfies t (F_Infinite (Atomic (eq b))).
Proof.
 cofix.
 intros q; case q.
 intros t Ht; case (from_q0 Ht). 
 intros x [tx [ea| eb]].
 rewrite ea; split.
 case (from_q2 tx).
 intros x0 [[t2| t1] e]; rewrite e; auto with llists.
 split.
 case (from_q2 tx).
 intros x0 [_ e]; rewrite e; auto with llists.
 apply Infinite_bs with q2; auto.
 rewrite eb; split.  
 auto with llists.
 case (from_q2 tx).
 intros x0 [_ e]; rewrite e.
 split.
 auto with llists. 
 case e; apply Infinite_bs with q2; auto.
 intros t Ht; case (from_q1 Ht).
 intros x [tx e]; rewrite e.
 split.
 case (from_q2 tx).
 intros x0 [_ e']; rewrite e'; auto with llists.
 apply Infinite_bs with q2; auto.
 intros t Ht; case (from_q2 Ht).
 intros x [[t1| t2] e]; rewrite e.  
 split.
 auto with llists.
 apply Infinite_bs with q2; auto.
 split.
 auto with llists.
 apply Infinite_bs with q1; auto.
Qed.

End exemple.

