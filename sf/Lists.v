(** * Lists: Working with Structured Data *)

Require Export Induction.

Module NatList. 

(* ###################################################### *)
(** * Pairs of Numbers *)

Inductive natprod : Type :=
  pair : nat -> nat -> natprod.

Check (pair 3 5).

(** *** *)

Definition fst (p : natprod) : nat := 
  match p with
  | pair x y => x
  end.
Definition snd (p : natprod) : nat := 
  match p with
  | pair x y => y
  end.

Eval compute in (fst (pair 3 5)).
(* ===> 3 *)

(** *** *)

Notation "( x , y )" := (pair x y).

Eval compute in (fst (3,5)).

Definition fst' (p : natprod) : nat := 
  match p with
  | (x,y) => x
  end.
Definition snd' (p : natprod) : nat := 
  match p with
  | (x,y) => y
  end.

Definition swap_pair (p : natprod) : natprod := 
  match p with
  | (x,y) => (y,x)
  end.

(** *** *)

Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity.  Qed.

Theorem surjective_pairing_stuck : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  simpl. (* Doesn't reduce anything! *)
Abort.

(** *** *)

Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p.  destruct p as [n m].  simpl.  reflexivity.  Qed.



(** **** Exercise: 1 star (snd_fst_is_swap)  *)
Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  destruct p. reflexivity.
Qed.
(** [] *)



(** **** Exercise: 1 star, optional (fst_swap_is_snd)  *)
Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  destruct p. reflexivity.
Qed.



(* ###################################################### *)
(** * Lists of Numbers *)

Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

(** *** *)

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

(** *** Repeat *)

Fixpoint repeat (n count : nat) : natlist := 
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

(** *** Length *)

Fixpoint length (l:natlist) : nat := 
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

(** *** Append *)

Fixpoint app (l1 l2 : natlist) : natlist := 
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y) 
                     (right associativity, at level 60).

Example test_app1:             [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity.  Qed.
Example test_app2:             nil ++ [4;5] = [4;5].
Proof. reflexivity.  Qed.
Example test_app3:             [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity.  Qed.

(** *** Head (with default) and Tail *)
Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l:natlist) : natlist :=
  match l with
  | nil => nil  
  | h :: t => t
  end.

Example test_hd1:             hd 0 [1;2;3] = 1.
Proof. reflexivity.  Qed.
Example test_hd2:             hd 0 [] = 0.
Proof. reflexivity.  Qed.
Example test_tl:              tl [1;2;3] = [2;3].
Proof. reflexivity.  Qed.



(** **** Exercise: 2 stars (list_funs)  *)
(** Complete the definitions of [nonzeros], [oddmembers] and
    [countoddmembers] below. Have a look at the tests to understand
    what these functions should do. *)

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => match h with
              | O => nonzeros t
              | S _ => h :: (nonzeros t)
              end
  end.

Example test_nonzeros:            nonzeros [0;1;0;2;3;0;0] = [1;2;3].
  reflexivity. 
Qed.

Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => match (oddb h) with
              | true => h :: (oddmembers t)
              | false => oddmembers t
              end
  end.

Example test_oddmembers:            oddmembers [0;1;0;2;3;0;0] = [1;3].
  reflexivity. 
Qed.

Fixpoint countoddmembers (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => match (oddb h) with
              | true => S (countoddmembers t)
              | false => countoddmembers t
              end
  end.

Example test_countoddmembers1:    countoddmembers [1;0;3;1;4;5] = 4.
  reflexivity. Qed.
Example test_countoddmembers2:    countoddmembers [0;2;4] = 0.
  reflexivity. Qed.
Example test_countoddmembers3:    countoddmembers nil = 0.
  reflexivity. Qed.
(** [] *)



(** **** Exercise: 3 stars, advanced (alternate)  *)
(** Complete the definition of [alternate], which "zips up" two lists
    into one, alternating between elements taken from the first list
    and elements from the second.  See the tests below for more
    specific examples.

    Note: one natural and elegant way of writing [alternate] will fail
    to satisfy Coq's requirement that all [Fixpoint] definitions be
    "obviously terminating."  If you find yourself in this rut, look
    for a slightly more verbose solution that considers elements of
    both lists at the same time.  (One possible solution requires
    defining a new kind of pairs, but this is not the only way.)  *)


Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h1 :: t1 => match l2 with
                | nil => l1
                | h2 :: t2 => h1 :: (h2 :: (alternate t1 t2))
                end
  end.


Example test_alternate1:        alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
  reflexivity. Qed.
Example test_alternate2:        alternate [1] [4;5;6] = [1;4;5;6].
  reflexivity. Qed.
Example test_alternate3:        alternate [1;2;3] [4] = [1;4;2;3].
  reflexivity. Qed.
Example test_alternate4:        alternate [] [20;30] = [20;30].
  reflexivity. Qed.
(** [] *)



(* ###################################################### *)
(** ** Bags via Lists *)

Definition bag := natlist.  



(** **** Exercise: 3 stars (bag_functions)  *)
(** Complete the following definitions for the functions
    [count], [sum], [add], and [member] for bags. *)

Fixpoint count (v:nat) (s:bag) : nat := 
  match s with
  | nil => O
  | h :: t => match (beq_nat h v) with
              | true => S (count v t)
              | false => count v t
              end
  end.

(** All these proofs can be done just by [reflexivity]. *)

Example test_count1:              count 1 [1;2;3;1;4;1] = 3.
  reflexivity. Qed.
Example test_count2:              count 6 [1;2;3;1;4;1] = 0.
  reflexivity. Qed.

(** Multiset [sum] is similar to set [union]: [sum a b] contains
    all the elements of [a] and of [b].  (Mathematicians usually
    define [union] on multisets a little bit differently, which
    is why we don't use that name for this operation.)
    For [sum] we're giving you a header that does not give explicit
    names to the arguments.  Moreover, it uses the keyword
    [Definition] instead of [Fixpoint], so even if you had names for
    the arguments, you wouldn't be able to process them recursively.
    The point of stating the question this way is to encourage you to
    think about whether [sum] can be implemented in another way --
    perhaps by using functions that have already been defined.  *)

Definition sum : bag -> bag -> bag := 
  app.

Example test_sum1:              count 1 (sum [1;2;3] [1;4;1]) = 3.
  reflexivity. Qed.


Definition add (v:nat) (s:bag) : bag := 
  v :: s.

Example test_add1:                count 1 (add 1 [1;4;1]) = 3.
  reflexivity. Qed.
Example test_add2:                count 5 (add 1 [1;4;1]) = 0.
  reflexivity. Qed.


Definition member (v:nat) (s:bag) : bool := 
  match (count v s) with
    | O => false
    | S _ => true
  end.

Example test_member1:             member 1 [1;4;1] = true.
  reflexivity. Qed.
Example test_member2:             member 2 [1;4;1] = false.
  reflexivity. Qed.
(** [] *)



(** **** Exercise: 3 stars, optional (bag_more_functions)  *)
(** Here are some more bag functions for you to practice with. *)

Fixpoint remove_one (v:nat) (s:bag) : bag :=
  match s with
  | nil => nil
  | h :: t => match (beq_nat v h) with
              | true => t
              | false => h :: (remove_one v t)
              end
  end.

Example test_remove_one1:         count 5 (remove_one 5 [2;1;5;4;1]) = 0.
  reflexivity. Qed.
Example test_remove_one2:         count 5 (remove_one 5 [2;1;4;1]) = 0.
  reflexivity. Qed.
Example test_remove_one3:         count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
  reflexivity. Qed.
Example test_remove_one4:         count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
  reflexivity. Qed.


Fixpoint remove_all (v:nat) (s:bag) : bag :=
  match s with
  | nil => nil
  | h :: t => match (beq_nat v h) with
              | true => remove_all v t
              | false => h :: (remove_all v t)
              end
  end.

Example test_remove_all1:          count 5 (remove_all 5 [2;1;5;4;1]) = 0.
  reflexivity. Qed.
Example test_remove_all2:          count 5 (remove_all 5 [2;1;4;1]) = 0.
  reflexivity. Qed.
Example test_remove_all3:          count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
  reflexivity. Qed.
Example test_remove_all4:          count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
  reflexivity. Qed.


Fixpoint subset (s1:bag) (s2:bag) : bool :=
  match s1 with
  | nil => true
  | h :: t => match (member h s2) with
              | true => subset t (remove_one h s2)
              | false => false
              end
  end.

Example test_subset1:              subset [1;2] [2;1;4;1] = true.
  reflexivity. Qed.
Example test_subset2:              subset [1;2;2] [2;1;4;1] = false.
  reflexivity. Qed.
(** [] *)



(** **** Exercise: 3 stars (bag_theorem)  *)
(** Write down an interesting theorem [bag_theorem] about bags involving
    the functions [count] and [add], and prove it.  Note that, since this
    problem is somewhat open-ended, it's possible that you may come up
    with a theorem which is true, but whose proof requires techniques
    you haven't learned yet.  Feel free to ask for help if you get
    stuck! *)

(* FILL IN HERE *)
(** [] *)



(* ###################################################### *)
(** * Reasoning About Lists *)

Theorem nil_app : forall l:natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  Case "l = nil".
    reflexivity.
  Case "l = n::l'". 
    reflexivity.  Qed.


(* ###################################################### *)
(** ** Micro-Sermon *)

(* ###################################################### *)
(** ** Induction on Lists *)

Theorem app_assoc : forall l1 l2 l3 : natlist, 
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).   
Proof.
  intros l1 l2 l3. induction l1 as [| n l1'].
  Case "l1 = nil".
    reflexivity.
  Case "l1 = n::l1'".
    simpl. rewrite -> IHl1'. reflexivity.  Qed.

(** *** Informal version *)


(** *** Another example *)

Theorem app_length : forall l1 l2 : natlist, 
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  (* WORKED IN CLASS *)
  intros l1 l2. induction l1 as [|h t].
  Case "l1 = nil".
    reflexivity.
  Case "l1 = h::t".
    simpl. rewrite -> IHt. reflexivity.  Qed.


(** *** Reversing a list *)

Fixpoint snoc (l:natlist) (v:nat) : natlist := 
  match l with
  | nil    => [v]
  | h :: t => h :: (snoc t v)
  end.

Fixpoint rev (l:natlist) : natlist := 
  match l with
  | nil    => nil
  | h :: t => snoc (rev t) h
  end.

Example test_rev1:            rev [1;2;3] = [3;2;1].
Proof. reflexivity.  Qed.
Example test_rev2:            rev nil = nil.
Proof. reflexivity.  Qed.

Theorem rev_length_firsttry : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l'].
  Case "l = []".
    reflexivity.
  Case "l = n :: l'".
    (* This is the tricky case.  Let's begin as usual 
       by simplifying. *)
    simpl. 
    (* Now we seem to be stuck: the goal is an equality 
       involving [snoc], but we don't have any equations 
       in either the immediate context or the global 
       environment that have anything to do with [snoc]! 

       We can make a little progress by using the IH to 
       rewrite the goal... *)
    rewrite <- IHl'.
    (* ... but now we can't go any further. *)
Abort.

Theorem length_snoc : forall n : nat, forall l : natlist,
  length (snoc l n) = S (length l).
Proof.
  intros n l. induction l as [| n' l'].
  Case "l = nil".
    reflexivity.
  Case "l = n'::l'".
    simpl. rewrite -> IHl'. reflexivity.  Qed. 


Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l'].
  Case "l = nil".
    reflexivity.
  Case "l = n::l'".
    simpl. rewrite -> length_snoc. 
    rewrite -> IHl'. reflexivity.  Qed.


(* ###################################################### *)
(** ** [SearchAbout] *)

(* ###################################################### *)
(** ** List Exercises, Part 1 *)

(** **** Exercise: 3 stars (list_exercises)  *)
(** More practice with lists. *)

Theorem app_nil_end : forall l : natlist, 
  l ++ [] = l.   
Proof.
  intro l.
  induction l as [|h l'].
  Case "l = nil".
    reflexivity.
  Case "l = h::l'".
    simpl. rewrite IHl'. reflexivity.
Qed.
  

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
Abort.

(** There is a short solution to the next exercise.  If you find
    yourself getting tangled up, step back and try to look for a
    simpler way. *)

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4.
  rewrite (app_assoc l1).
  rewrite (app_assoc l1 _ l4).
  rewrite (app_assoc l2).
  reflexivity.
Qed.

Theorem snoc_append : forall (l:natlist) (n:nat),
  snoc l n = l ++ [n].
Proof.
  intros l n.
  induction l as [|h l'].
  Case "l = nil".
    reflexivity.
  Case "l = h::l'".
    simpl. rewrite IHl'. reflexivity.
Qed.

Theorem distr_rev : forall l1 l2 : natlist,
  rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof.
  intros l1 l2.
  induction l1 as [|h1 l1'].
  Case "l1 = nil".
    simpl. rewrite app_nil_end. reflexivity.
  Case "l1 = h1::l1'".
    simpl. rewrite IHl1'. rewrite snoc_append.
    rewrite app_assoc. rewrite snoc_append.
    reflexivity.
Qed.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intro l.
  induction l as [|h t].
  Case "l = nil".
    reflexivity.
  Case "l = h::t".
    simpl. rewrite snoc_append. 
    rewrite distr_rev.
    simpl. rewrite IHt. reflexivity.
Qed.

(** An exercise about your implementation of [nonzeros]: *)

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2.
  induction l1 as [|h1 l1'].
  Case "l1 = nil".
    reflexivity.
  Case "l1 = h1::l1'".
    destruct h1 as [|h1'].
    SCase "h1 = 0".
      simpl. rewrite IHl1'. reflexivity.
    SCase "h1 = S h1'".
      simpl. rewrite IHl1'. reflexivity.
Qed.
(** [] *)



(** **** Exercise: 2 stars (beq_natlist)  *)
(** Fill in the definition of [beq_natlist], which compares
    lists of numbers for equality.  Prove that [beq_natlist l l]
    yields [true] for every list [l]. *)

Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
  match l1 with
  | nil => match l2 with
           | nil => true
           | _ :: _ => false
           end
  | h1 :: t1 => match l2 with
                | nil => false
                | h2 :: t2 => match (beq_nat h1 h2) with
                              | true => beq_natlist t1 t2
                              | false => false
                              end
                end
  end.

Example test_beq_natlist1 :   (beq_natlist nil nil = true).
  reflexivity. Qed.
Example test_beq_natlist2 :   beq_natlist [1;2;3] [1;2;3] = true.
  reflexivity. Qed.
Example test_beq_natlist3 :   beq_natlist [1;2;3] [1;2;4] = false.
  reflexivity. Qed.

Theorem beq_natlist_refl : forall l:natlist,
  true = beq_natlist l l.
Proof.
  intro l.
  induction l as [|h t].
  Case "l = nil".
    reflexivity.
  Case "l = h :: t".
    simpl. 
    assert (H: beq_nat h h = true).
    SCase "proof of (beq_nat h h) = true".
      induction h as [|h'].
      SSCase "h = 0".
        reflexivity.
      SSCase "h = S h'".
        simpl. rewrite IHh'. reflexivity.
    rewrite H. rewrite IHt. reflexivity.
Qed.
(** [] *)



(* ###################################################### *)
(** ** List Exercises, Part 2 *)

(** **** Exercise: 2 stars (list_design)  *)
(** Design exercise: 
     - Write down a non-trivial theorem [cons_snoc_app]
       involving [cons] ([::]), [snoc], and [app] ([++]).  
     - Prove it. *) 

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 3 stars, advanced (bag_proofs)  *)
(** Here are a couple of little theorems to prove about your
    definitions about bags earlier in the file. *)

Theorem count_member_nonzero : forall (s : bag),
  ble_nat 1 (count 1 (1 :: s)) = true.
Proof.
  intro s.
  destruct s as [|h t].
  Case "s = nil".
    reflexivity.
  Case "s = h :: t".
    reflexivity.
Qed.

(** The following lemma about [ble_nat] might help you in the next proof. *)

Theorem ble_n_Sn : forall n,
  ble_nat n (S n) = true.
Proof.
  intros n. induction n as [| n'].
  Case "0".  
    simpl.  reflexivity.
  Case "S n'".
    simpl.  rewrite IHn'.  reflexivity.  Qed.

Theorem remove_decreases_count: forall (s : bag),
  ble_nat (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
  intro s.
  induction s as [|h t].
  Case "s = nil".
    reflexivity.
  Case "s = h :: t".
    simpl.
    destruct h as [|h'].
    SCase "h = 0".
      simpl. rewrite ble_n_Sn. reflexivity.
    SCase "h = S h'".
      simpl. rewrite IHt. reflexivity.
Qed.
(** [] *)



(** **** Exercise: 3 stars, optional (bag_count_sum)  *)  
(** Write down an interesting theorem [bag_count_sum] about bags 
    involving the functions [count] and [sum], and prove it.*)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 4 stars, advanced (rev_injective)  *)
(** Prove that the [rev] function is injective, that is,

    forall (l1 l2 : natlist), rev l1 = rev l2 -> l1 = l2.

There is a hard way and an easy way to solve this exercise.
*)

Theorem rev_inj : forall (l1 l2 : natlist), 
  rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1 l2. intros H.
  rewrite <- (rev_involutive l1).
  rewrite <- (rev_involutive l2).
  rewrite H.
  reflexivity.
Qed.
  
(* FILL IN HERE *)
(** [] *)


(* ###################################################### *)
(** * Options *)

Fixpoint index_bad (n:nat) (l:natlist) : nat :=
  match l with
  | nil => 42  (* arbitrary! *)
  | a :: l' => match beq_nat n O with 
               | true => a 
               | false => index_bad (pred n) l' 
               end
  end.


Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.  


Fixpoint index (n:nat) (l:natlist) : natoption :=
  match l with
  | nil => None 
  | a :: l' => match beq_nat n O with 
               | true => Some a
               | false => index (pred n) l' 
               end
  end.

Example test_index1 :    index 0 [4;5;6;7]  = Some 4.
Proof. reflexivity.  Qed.
Example test_index2 :    index 3 [4;5;6;7]  = Some 7.
Proof. reflexivity.  Qed.
Example test_index3 :    index 10 [4;5;6;7] = None.
Proof. reflexivity.  Qed.

(** *** *)

Fixpoint index' (n:nat) (l:natlist) : natoption :=
  match l with
  | nil => None 
  | a :: l' => if beq_nat n O then Some a else index' (pred n) l'
  end.


Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.



(** **** Exercise: 2 stars (hd_opt)  *)
(** Using the same idea, fix the [hd] function from earlier so we don't
   have to pass a default element for the [nil] case.  *)

Definition hd_opt (l : natlist) : natoption :=
  match l with
  | nil => None
  | h :: _ => Some h
  end.

Example test_hd_opt1 : hd_opt [] = None.
  reflexivity. Qed.

Example test_hd_opt2 : hd_opt [1] = Some 1.
  reflexivity. Qed.

Example test_hd_opt3 : hd_opt [5;6] = Some 5.
  reflexivity. Qed.
(** [] *)



(** **** Exercise: 1 star, optional (option_elim_hd)  *)
(** This exercise relates your new [hd_opt] to the old [hd]. *)

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_opt l).
Proof.
  intros l default.
  destruct l as [|h t].
  Case "l = nil".
    reflexivity.
  Case "l = h::t".
    reflexivity.
Qed.
(** [] *)



(* ###################################################### *)
(** * Dictionaries *)

Module Dictionary.

Inductive dictionary : Type :=
  | empty  : dictionary 
  | record : nat -> nat -> dictionary -> dictionary. 


Definition insert (key value : nat) (d : dictionary) : dictionary :=
  (record key value d).


Fixpoint find (key : nat) (d : dictionary) : natoption := 
  match d with 
  | empty         => None
  | record k v d' => if (beq_nat key k) 
                       then (Some v) 
                       else (find key d')
  end.



(** **** Exercise: 1 star (dictionary_invariant1)  *)
(** Complete the following proof. *)

Theorem dictionary_invariant1' : forall (d : dictionary) (k v: nat),
  (find k (insert k v d)) = Some v.
Proof.
  intros d k v.
  simpl. 
  assert (H: beq_nat k k = true).
  Case "proof of (beq_nat k k) = true".
    induction k as [|k'].
    SCase "k = 0".
      reflexivity.
    SCase "k = S k'".
      simpl. rewrite IHk'. reflexivity.
  rewrite H. reflexivity.
Qed.
(** [] *)



(** **** Exercise: 1 star (dictionary_invariant2)  *)
(** Complete the following proof. *)

Theorem dictionary_invariant2' : forall (d : dictionary) (m n o: nat),
  beq_nat m n = false -> find m d = find m (insert n o d).
Proof.
  intros d m n o. intros H.
  simpl. rewrite H. reflexivity.
Qed.
(** [] *)



End Dictionary.

End NatList.

(** $Date: 2014-12-31 11:17:56 -0500 (Wed, 31 Dec 2014) $ *)

