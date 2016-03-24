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
  | prO : pr
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

