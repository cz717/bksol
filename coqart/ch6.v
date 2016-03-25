(** ** Chapter 6. Inductive Data Types *)

Inductive month : Set :=
  | January   | February | March    | April
  | May       | June     | July     | August
  | September | October  | November | December.

(** Exercise 6.1 *)

Inductive season : Set :=
  | Spring | Summer | Autumn | Winter.

Definition mtos : month -> season :=
  month_rec (fun x:month => season)
            Winter Spring Spring Spring Summer Summer
            Summer Autumn Autumn Autumn Winter Winter.

(** [] *)


Definition month_length (leap:bool) (m:month) : nat :=
  match m with
    | February => if leap then 29 else 28
    | April | June | September | November => 30
    | _ => 31
  end.


(** Exercise 6.17 *)

Require Import ZArith.

Fixpoint sum_f (f : nat -> Z) (n : nat) : Z :=
  match n with
    | 0 => f 0
    | S n' => f n + (sum_f f n')
  end.

(** [] *)


(** Exercise 6.20 *)

Fixpoint pos_even_bool (p : positive) : bool :=
  match p with
    | xH => false
    | xO _ => true
    | xI _ => false
  end.

(** [] *)


(** Exercise 6.21 *)

Fixpoint pos_div4 (p : positive) : Z :=
  match p with
    | xH => 0
    | xO x | xI x =>
             match x with
               | xH => 0
               | xO y | xI y => Zpos y
             end
  end.

(** [] *)


(** Exercise 6.22 *)

Parameter pos_mult : positive -> positive -> positive.

Fixpoint z_mult (n m : Z) : Z :=
  match n with
    | Z0 => 0
    | Zpos a => match m with
                  | Z0 => 0
                  | Zpos b => Zpos (pos_mult a b)
                  | Zneg b => Zneg (pos_mult a b)
                end
    | Zneg a => match m with
                  | Z0 => 0
                  | Zpos b => Zneg (pos_mult a b)
                  | Zneg b => Zpos (pos_mult a b)
                end
  end.

(** [] *)


(** Exercise 6.23 *)

Inductive Prop_Logic : Set :=
  | L_True | L_False
  | L_Conj : Prop_Logic -> Prop_Logic -> Prop_Logic
  | L_Disj : Prop_Logic -> Prop_Logic -> Prop_Logic
  | L_Neg : Prop_Logic -> Prop_Logic
  | L_Imp : Prop_Logic -> Prop_Logic -> Prop_Logic.

(** [] *)


(** Exercise 6.24 *)

Inductive pr : Set :=
  | prI : pr
  | prN : pr -> pr
  | prD : pr -> pr.

(** [] *)


(** Exercise 6.25 *)

Inductive Z_btree : Set :=
  | Z_leaf : Z_btree
  | Z_node : Z -> Z_btree -> Z_btree -> Z_btree.

Fixpoint value_present (z : Z) (t : Z_btree) : bool :=
  match t with
    | Z_leaf => false
    | Z_node x l r => if Zeq_bool z x
                      then true
                      else orb (value_present z l) 
                               (value_present z r)
  end.

(** [] *)


(** Exercise 6.26 *)

Fixpoint power (x : Z) (e : nat) : Z :=
  match e with
    | 0 => 1
    | S e' => x * (power x e')
  end.

Fixpoint discrete_log (p : positive) : nat :=
  match p with
    | xH => 0
    | xO p' | xI p' => S (discrete_log p')
  end.

(** [] *)


Inductive Z_fbtree : Set :=
  | Z_fleaf : Z_fbtree
  | Z_fnode : Z -> (bool -> Z_fbtree) -> Z_fbtree.


(** Exercise 6.27 *)

Fixpoint fzero_present (t : Z_fbtree) : bool :=
  match t with 
    | Z_fleaf => false
    | Z_fnode z f => match z with
                       | 0%Z => true
                       | _ => orb (fzero_present (f true))
                                  (fzero_present (f false))
                     end
  end.

(** [] *)

Inductive Z_inf_branch_tree : Set :=
  | Z_inf_leaf : Z_inf_branch_tree
  | Z_inf_node : Z -> (nat -> Z_inf_branch_tree) -> Z_inf_branch_tree.


(** Exercise 6.28 *)

Fixpoint inf_zero_present (n : nat) (t : Z_inf_branch_tree) : bool := 
  match t with 
    | Z_inf_leaf => false
    | Z_inf_node z f => 
        match z with
          | 0%Z => true
          | _ => (fix f (g:nat->bool)(m:nat){struct m}:bool :=
                    match m with
                      | 0 => g 0
                      | S m' => orb (g m) (f g m')
                    end)
                 (fun (m:nat) => (inf_zero_present n (f m)))
                 n
        end
  end.

(** [] *)


(** Exercise 6.30 *)

Fixpoint f1 (t : Z_btree) : Z_fbtree :=
  match t with
    | Z_leaf => Z_fleaf
    | Z_node z l r => Z_fnode z (fun b => match b with
                                            | true => (f1 l)
                                            | false => (f1 r)
                                          end)
  end.

Fixpoint f2 (ft : Z_fbtree) : Z_btree :=
  match ft with
    | Z_fleaf => Z_leaf
    | Z_fnode z f => Z_node z (f2 (f true)) (f2 (f false))
  end.

Theorem f21 : forall t:Z_btree, f2 (f1 t) = t.
Proof.
  intros t. induction t as [|z l IHl r IHr].
  - trivial.
  - simpl. rewrite IHl. rewrite IHr. reflexivity.
Qed.

Theorem f12 : forall ft : Z_fbtree, f1 (f2 ft) = ft.
Proof.
  intros ft. induction ft as [|z f IH].
  - trivial.
  - simpl. rewrite (IH true). rewrite (IH false).
Abort.

(** [] *)


(** Exercise 6.32 *)

Fixpoint sum_n (n : nat) : nat :=
  match n with
    | 0 => 0
    | S n' => n + sum_n n'
  end.

Theorem sn : forall n:nat, 2 * sum_n n = n * S n.
Proof.
  induction n as [|n'].
  - trivial.
  - simpl (sum_n _).
    rewrite <- plus_Sn_m.
    rewrite mult_plus_distr_l.
    rewrite IHn'.
    rewrite <- mult_plus_distr_r.
    rewrite mult_comm.
    simpl. reflexivity.
Qed.

(** [] *)


(** Exercise 6.33 *)

Theorem nlesn : forall n, n <= sum_n n.
Proof.
  induction n as [|n'].
  - trivial.
  - simpl. apply le_n_S.
    rewrite plus_comm.
    apply le_plus_trans.
    assumption.
Qed.

(** [] *)


Fixpoint nth_option (A : Set) (n : nat) (l : list A) {struct l} : option A :=
  match n, l with
    | 0, cons h _ => Some h
    | S p, cons h t => nth_option A p t
    | _ , nil => None
  end.


(** Exercise 6.40 *)

Theorem ex40 : forall  (A : Set) (n : nat) (l : list A),
  nth_option A n l = None -> length l <= n.
Proof.
  intros A n l.
  generalize dependent n.
  induction l as [|h t]; intros n.
  - intros H. simpl. apply le_0_n.
  - intros H. simpl. 
    destruct n as [|n'].
    + inversion H.
    + simpl in H. 
      apply le_n_S. apply IHt. assumption.
Qed.

(** [] *)


(** Exercise 6.41 *)

Fixpoint ft (A : Set) (f : A -> bool) (l : list A) : option A :=
  match l with
    | nil => None
    | cons h t => if f h then Some h else ft A f t
  end.

(** [] *)



(** Exercise 6.44 *)
Open Scope positive_scope.

Fixpoint nd (r : pr) : positive*positive :=
  match r with
    | prI => (1, 1)
    | prN r' => let (n, d) := nd r'
               in (n+d, d)
    | prD r' => let (n, d) := nd r'
               in (n, n+d)
  end.

Close Scope positive_scope.
(** [] *)


(** Exercise 6.45 *)
Require Import List.

Inductive cmp : Set :=
  Less : cmp
| Equal : cmp
| Greater : cmp.

Fixpoint three_way_compare (n m : nat){struct n} : cmp :=
  match n, m with
    | 0, 0 => Equal
    | 0, S _ => Less
    | S _, 0 => Greater
    | S n', S m' => three_way_compare n' m'
  end.

Fixpoint update_primes (k:nat) (l: list (nat*nat)) : (list (nat*nat)) * bool :=
  match l with
    | nil => (nil, false)
    | cons (p, m) t =>
        match (three_way_compare m k) with
          | Equal => let (t', b) := update_primes k t
                     in ((cons (p, m + p) t'), true)
          | _ => let (t', b) := update_primes k t
                 in ((cons (p, m) t'), b)
        end
  end.

Fixpoint prime_sieve (k : nat) : list (nat*nat) :=
  match k with
    | 0 => nil
    | 1 => nil
    | S k' => let l' := prime_sieve k'
              in  match update_primes k l' with
                    | (l, true) => l
                    | (l, false) => cons (k, k*2) l
                  end
  end.

(** proof here *)

(** [] *)



Inductive htree (A : Set) : nat -> Set :=
| hleaf : A -> htree A 0
| hnode : forall n : nat, A -> htree A n -> htree A n -> htree A (S n).


(** Exercise 6.46 *)

Fixpoint pre (n : nat) : nat :=
  match n with
    | 0 => 0
    | S n' => n'
  end.

Definition aux (n : nat) (t : htree nat n) : htree nat (pre n) :=
  match t with
    | hleaf _ a => hleaf _ a
    | hnode _ n' a l r => l
  end.

Theorem ex46 : forall (n:nat) (t1 t2 t3 t4 : htree nat n),
  hnode nat n 0 t1 t2 = hnode nat n 0 t3 t4 -> t1 = t3.
Proof.
  intros n t1 t2 t3 t4 H.
  change ((aux (S n) (hnode nat n 0 t1 t2)) = (aux (S n) (hnode nat n 0 t3 t4))).
  rewrite H. simpl. reflexivity.
Qed.

(** [] *)


(** Exercise 6.32 *)

Inductive binary_word : nat -> Set :=
| bw : forall (n : nat) (l : list bool), length l = n -> binary_word n.

Fixpoint binary_word_concat (n m : nat) (nbw : binary_word n) (mbw : binary_word m) 
  : binary_word (n + m).
(* Define *)
  destruct nbw as [n nl len].
  destruct mbw as [m ml lem].
  apply (bw (n + m) (nl ++ ml)).
  rewrite <- len.
  rewrite <- lem.
  apply app_length.
Defined.

(** [] *)


(** Exercise 6.49 *)

Fixpoint map2 {A B : Set} (f : A -> A -> B) (l1 l2 : list A) {struct l1} : list B :=
  match l1, l2 with
    | nil, _ => nil
    | _, nil => nil
    | h1::t1, h2::t2 => (f h1 h2) :: (map2 f t1 t2)
  end.

Lemma map2_length : forall (A B : Set ) (l1 l2 : list A) (f : A -> A -> B) (n : nat),
  length l1 = n -> length l2 = n -> length (map2 f l1 l2) = n.
Proof.
  intros A B l1 l2 f n.
  generalize dependent l2.
  generalize dependent l1.
  induction n as [|n']; intros l1 l2 len1 len2.
  - rewrite length_zero_iff_nil in len1.
    rewrite length_zero_iff_nil in len2.
    rewrite len1. rewrite len2. trivial.
  - destruct l1 as [|h1 t1]; inversion len1.
    simpl in len1.
    destruct l2 as [|h2 t2]; inversion len2.
    simpl. rewrite H0.
    cut ((length (map2 f t1 t2)) = n').
    + intros H. rewrite H. reflexivity.
    + apply (IHn' t1 t2 H0 H1).
Qed.

Definition binary_word_or (n : nat) (bw1 bw2 : binary_word n) : binary_word n.
(* Definition *)
  destruct bw1 as [n l1 len1].
  destruct bw2 as [n l2 len2].
  apply (bw n (map2 orb l1 l2)).
  apply map2_length; assumption.
Defined.

(** [] *)


(** Exercise 6.50 *)
(* Abort *)
(** [] *)