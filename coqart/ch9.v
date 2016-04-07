
(* ** Chapter 9. Functions and their Specifications *)

Require Export ZArith.
Require Export List.
Require Export Arith.
Require Export Omega.
Require Export Zwf.

Parameter prime : nat->Prop.

Section div_pair_section.
 Open Scope Z_scope.
 Variable div_pair :
   forall a b:Z, 0 < b -> 
                 {p:Z*Z | a = (fst p)*b + snd p /\ 0 <= snd p < b}.

 Definition div_pair' (a:Z)(x:{b:Z | 0 < b}) : Z*Z :=
   match x with
   | exist _ b h => let (v, _) := div_pair a b h in v
   end.


(** Exercise 9.1 *)

Definition extract (A : Set) (P : A -> Prop) (s : sig P) : A :=
  match s with
    | exist _ x H => x
  end.

Theorem ext_sig : forall (A : Set) (P : A -> Prop) (y : {x:A | P x}),
  P (extract A (fun x:A => P x ) y).
Proof.
  intros A P [x h].
  unfold extract. assumption.
Qed.

(** [] *)


(** Exercise 9.2 *)

Definition div_pair'' (a : Z) (x : {b:Z | 0 < b})
: {p:Z*Z | a = (fst p) * (extract _ _ x) + snd p /\ 0 <= snd p < (extract _ _ x)}.
(* Define *)
  destruct x as [b h].
  apply (div_pair a b h).
Defined.

(** [] *)


(** Exercise 9.3 *)

Definition sig_rec_simple (A : Set) (P : A -> Prop) (B : Set)
  (h: (forall x : A, P x -> B)) (s: sig P) : B
:=
  match s with
    | exist _ x H => h x H
  end.

(** [] *)

End div_pair_section.


Section div2_of_even_section.
Open Scope nat_scope.

 Variable even : nat->Prop.
 Variables (div2_of_even : forall n:nat, even n -> {p:nat | n = p+p})
           (test_even : forall n:nat, {even n}+{even (pred n)} ).

 Definition div2_gen (n:nat) :
   {p:nat | n = p+p}+{p:nat | pred n = p+p} :=
   match test_even n with
   | left h => inl _ (div2_of_even n h)
   | right h' => inr _ (div2_of_even (pred n) h')
   end.
End div2_of_even_section.


Definition eq_dec (A:Type) := forall x y:A, {x = y}+{x <> y}.

(** Exercis 9.4 *)

Definition nat_eq_dec : eq_dec nat.
  unfold eq_dec.
  induction x as [|x'].
  - destruct y as [|y'].
    + left. reflexivity.
    + right. trivial.
  - destruct y as [|y'].
    + right. auto.
    + destruct (IHx' y') as [L|R].
      * left. auto.
      * right. auto.
Defined.

(** [] *)


(** Exercise 9.5 *)

Fixpoint count (l : list nat) (x : nat) : nat :=
  match l with
    | nil => 0
    | h::t => match (nat_eq_dec x h) with
                | left _ => S (count t x)
                | right _ => count t x
              end
  end.

(** [] *)


Open Scope nat_scope.

Definition pred' (n:nat) : {p:nat | n = S p}+{n = 0} :=
  match n return {p:nat | n = S p}+{n = 0} with
  | O => inright _ (refl_equal 0)
  | S p =>
     inleft _ 
       (exist (fun p':nat => S p = S p') p (refl_equal (S p)))
  end.

Reset pred'.
Definition pred' : forall n:nat, {p:nat | n = S p}+{n = 0}.
 intros n; case n.
 right; apply refl_equal.
 intros p; left; exists p; reflexivity.
Defined.


Definition pred_partial : forall n:nat, n <> 0 -> nat.
 intros n; case n.
 intros h; elim h; reflexivity.
 intros p h'; exact p.
Defined.

Theorem le_2_n_not_zero : forall n:nat, 2 <= n -> n <> 0.
Proof.
 intros n Hle; elim Hle; intros; discriminate.
Qed.

Theorem le_2_n_pred :
 forall (n:nat)(h: 2 <= n), pred_partial n (le_2_n_not_zero n h) <> 0.
 (*
 intros n h; elim h.
 *)
Abort.

Theorem le_2_n_pred' :
 forall n:nat, 2 <= n -> forall h:n <> 0, pred_partial n h <> 0.
Proof.
 intros n Hle; elim Hle.
 intros; discriminate.
 simpl; intros; apply le_2_n_not_zero; assumption.
Qed.

Theorem le_2_n_pred :
 forall (n:nat)(h:2 <= n), pred_partial n (le_2_n_not_zero n h) <> 0.
Proof.
 intros n h; exact (le_2_n_pred' n h (le_2_n_not_zero n h)).
Qed.

Definition pred_partial_2 (n:nat)(h:2 <= n) : nat :=
  pred_partial (pred_partial n (le_2_n_not_zero n h)) 
               (le_2_n_pred n h).

Definition pred_strong : forall n:nat, n <> 0 -> {v:nat | n = S v}.
 intros n; case n; 
  [intros H; elim H | intros p H'; exists p]; trivial.
Defined.

Theorem pred_strong2_th1 :
 forall n p:nat, 2 <= n -> n = S p -> p <> 0.
Proof.
 intros; omega.
Qed.

Theorem pred_th1 : forall n p q:nat, n = S p -> p = S q -> n = S (S q).
Proof.
 intros; subst n; auto.
Qed.

Definition pred_strong2 (n:nat)(h:2<=n):{v:nat | n = S (S v)} :=
  match pred_strong n (le_2_n_not_zero n h) with
  | exist _ p h' =>
      match pred_strong p (pred_strong2_th1 n p h h') with
      | exist _ p' h'' =>
          exist (fun x:nat => n = S (S x)) 
                p' (pred_th1 n p p' h' h'')
      end
  end.

Definition pred_strong2' :
  forall n:nat, 2 <= n -> {v:nat | n = S (S v)}.
 intros n h; case (pred_strong n).
 apply le_2_n_not_zero; assumption.
 intros p h'; case (pred_strong p).
 apply (pred_strong2_th1 n); assumption.
 intros p' h''; exists p'.
 eapply pred_th1; eauto.
Defined.


Section minimal_specification_strengthening.
 
 Variable prime : nat->Prop.
 Definition divides (n p:nat) : Prop := exists q:_, q*p = n.
 Definition prime_divisor (n p:nat):= prime p /\ divides p n.

 Variable prime_test : nat->bool.
 Hypotheses
   (prime_test_t : forall n:nat, prime_test n = true -> prime n)
   (prime_test_f : forall n:nat, prime_test n = false -> ~prime n).

 Variable get_primediv_weak : forall n:nat, ~prime n -> nat.
 Hypothesis get_primediv_weak_ok :
     forall (n:nat)(H:~prime n), 1 < n ->
        prime_divisor n (get_primediv_weak n H).


 Lemma divides_refl : forall n:nat, divides n n.
  Proof.
  intro n; exists 1; simpl; auto.
 Qed.
 Hint Resolve divides_refl.

 Definition bad_get_prime : nat->nat.
  intro n; case_eq (prime_test n).
  intro; exact n.
  intro Hfalse; apply (get_primediv_weak n); auto.
 Defined.

 Theorem bad_get_primediv_ok :
  forall n:nat, 1 < n -> prime_divisor n (bad_get_prime n).
 Proof.
  intros n H; unfold bad_get_prime.
 Abort.

 Definition stronger_prime_test :
   forall n:nat, {(prime_test n)=true}+{(prime_test n)=false}.
  intro n; case (prime_test n);[left | right]; reflexivity.
 Defined.

 Definition get_prime (n:nat) : nat :=
  match stronger_prime_test n with
  | left H => n
  | right H => get_primediv_weak n (prime_test_f n H)
  end.
 
 Theorem get_primediv_ok :
  forall n:nat, 1 < n -> prime_divisor n (get_prime n).
 Proof.
  intros n H; unfold get_prime.
  case (stronger_prime_test n); auto.
  split; auto.
 Qed.

End minimal_specification_strengthening.


Definition pred_partial' : forall n:nat, n <> 0 -> nat.
 refine
  (fun n =>
    match n as x return x <> 0 -> nat with
    | O => fun h:0 <> 0 => _
    | S p => fun h:S p <> 0 => p
    end).
 elim h; trivial. 
Defined.

Definition pred_partial_2' : forall n:nat, le 2 n -> nat.
 refine
  (fun n h=>(fun h':n<>0 => pred_partial (pred_partial n h') _) _).
 apply le_2_n_pred'; auto.
 apply le_2_n_not_zero; auto.
Defined.

Definition pred_strong2'' : forall n:nat, 2<=n -> {v:nat | n = S (S v)}.
 refine
  (fun n h =>
    match pred_strong n _ with
    | exist _ p h' =>
      match pred_strong p _ with exist _ p' h'' => exist _ p' _ end
    end).
 apply le_2_n_not_zero; assumption.
 eapply pred_strong2_th1; eauto.
 rewrite <- h''; trivial.
Qed.


Require Import Program.
Program  Definition pred_strong2''' (n:nat)(H:2<=n):{v:nat|n = S (S v)} :=
    pred  (pred n ).
Require Import Omega.
Next Obligation.
(*

1 subgoal
  
  n : nat
  H : 2 <= n
  ============================
   n = S (S (pred (pred n)))

*)
omega.
Defined.


Fixpoint div2 (n:nat) : nat :=
  match n with 0 => 0 | 1 => 0 | S (S p) => S (div2 p) end.

Section bad_proof_for_div2_le.

 Theorem div2_le : forall n:nat, div2 n <= n.
 Proof.
  induction n.
  simpl; auto.
  induction n.
  simpl.
  auto.
 Abort.
End bad_proof_for_div2_le.

Theorem div2_le : forall n:nat, div2 n <= n.
Proof.
 intro n.
 cut (div2 n <= n /\ div2 (S n) <= S n).
 tauto.
 elim n.
 simpl; auto.
  intros p [H1 H2].
  split; auto.
  simpl; auto with arith.
Qed.


(** Exercise 9.6 *)

Fixpoint div3 (x:nat) : nat :=
  match x with
    | 0 => 0
    | 1 => 0
    | 2 => 0
    | S (S (S p)) => S (div3 p)
  end.

Theorem div3_le : forall n : nat, div3 n <= n.
Proof.
  intros n.
  cut (div3 n <= n /\ div3 (S n) <= (S n) /\ div3 (S (S n)) <= S (S n)).
  - tauto.
  - induction n as [|n'].
    + auto.
    + destruct IHn' as [H1 [H2 H3]].
      split; try split; try tauto.
      simpl. auto with arith.
Qed.

(** [] *)


(** Exercise 9.7 *)

Fixpoint mod2 (n : nat) : nat :=
  match n with
    | 0 => 0
    | 1 => 1
    | S (S p) => mod2 p
  end.

Theorem mod2_ok : forall n : nat, n = 2 * (div2 n) + (mod2 n).
Proof.
  intros n.
  cut (n = 2 * (div2 n) + (mod2 n)
      /\ (S n) = 2 * (div2 (S n)) + (mod2 (S n))).
  tauto.
  induction n as [|n'].
  - auto.
  - destruct IHn' as [H1 H2].
    split.
    + assumption.
    + simpl in H1. rewrite <- plus_n_O in H1.
      simpl. rewrite <- plus_n_O.
      rewrite <- plus_n_Sm. simpl.
      rewrite H1 at 1. reflexivity.
Qed.      

(** [] *)      


(** Exercise 9.8 *)

Fixpoint fib (n : nat) : nat :=
  match n with
    | 0 => 1
    | S p => match p with
               | 0 => 1
               | S q => fib q + fib p
             end
  end.

Fixpoint fib2 (n : nat) : nat*nat :=
  match n with
    | 0 => (1, 1)
    | S p => (snd (fib2 p), (fst (fib2 p)) + (snd (fib2 p)))
end.

Theorem fib_eq : forall n : nat, fib n = fst(fib2 n).
Proof.
  intros n.
  cut (fib n = fst (fib2 n) /\ fib (S n) = fst (fib2 (S n))).
  tauto.
  induction n as [|n'].
  - auto.
  - destruct IHn' as [H1 H2].
    split; try assumption.
    cut (fib n' + fib (S n') = fst (fib2 (S (S n')))).
    + trivial.
    + rewrite H1. rewrite H2.
      simpl fib2. simpl fst.
      reflexivity.
Qed.

(** [] *)


Theorem nat_2_ind :
 forall P:nat->Prop, P 0 -> P 1 ->(forall n:nat, P n -> P (S (S n)))->
   forall n:nat, P n.
Proof.
 intros P H0 H1 Hrec n; cut (P n /\ P (S n)).
 tauto. 
 elim n; intuition.
Qed.


(** Exercise 9.9 *)

Theorem nat_3_ind : forall P : nat -> Prop,
  P 0 -> P 1 -> P 2 -> (forall n : nat, P n -> P (S (S (S n)))) 
  -> forall n : nat, P n.
Proof.
  intros P H0 H1 H2 Hrec n.
  cut (P n /\ P (S n) /\ P (S (S n))).
  tauto.
  elim n; intuition.
Qed.

(** [] *)


(** Exercise 9.10 *)

Theorem nat_fib_ind : forall P : nat -> Prop,
  P 0 -> P 1 -> (forall n : nat, P n -> P (S n) -> P (S (S n)))
  -> (forall n : nat, P n).
Proof.
  intros P H0 H1 Hrec n.
  cut (P n /\ P (S n)).
  tauto.
  elim n; intuition.
Qed.


Lemma fib_ssn : forall n : nat, fib (S (S n)) = fib n + fib (S n).
Proof.
  intros n. auto.
Qed.

Lemma dp : forall n : nat, 2 * n = n + n.
Proof.
  induction n.
  - trivial.
  - simpl. rewrite <- plus_n_O. reflexivity.
Qed.

Create HintDb fibdb.
Hint Resolve fib_ssn : fibdb.
Hint Resolve dp : arith.

Theorem fibthm : forall n p, 
  fib (n+p+2) = (fib (n+1)) * (fib (p+1)) + (fib n) * (fib p).
Proof.
  intros n p.
  induction n using nat_fib_ind.
  - simpl. rewrite <- plus_n_O. 
    rewrite <- plus_n_O.
    rewrite plus_comm. 
    rewrite plus_comm with (m:= (fib p)). 
    rewrite plus_comm with (m:= 1).
    auto.
  - rewrite plus_comm with (m:=2).
    rewrite plus_comm with (n:=p)(m:=1).
    simpl plus at 1.
    rewrite fib_ssn.
    simpl (fib(1+1)). simpl (fib 1).
    simpl (1+p). rewrite mult_1_l.
    rewrite fib_ssn. 
    rewrite dp. 
    ring.
  - rewrite <- plus_assoc with (n:=(S (S n))).
    simpl (S _ + _).  
    rewrite fib_ssn.
    rewrite plus_assoc.
    rewrite <- plus_Sn_m.
    rewrite <- plus_Sn_m.
    rewrite IHn. rewrite IHn0.
    repeat rewrite fib_ssn.
    repeat rewrite mult_plus_distr_r.
    simpl (S _ + _).
    ring.
Qed.
    
(** [] *)


(** Exercise 9.11 *)
(** [] *)


Fixpoint div2'_aux (n:nat) : nat*nat :=
  match n with
  | 0 => (0, 0)
  | S p => let (v1,v2) := div2'_aux p in (v2, S v1)
  end.

Definition div2' (n:nat) : nat := fst (div2'_aux n).


(** Exercise 9.12 *)

Fixpoint mult2 (n:nat) : nat :=
  match n with
  | O => 0%nat
  | S p => S (S (mult2 p))
  end.

Definition div2_mod2 : 
  forall n:nat, {q:nat & {r:nat | n = 2*q + r /\ r <= 1}}.
(* Define *)
  intros n.
  apply (existS _ (div2 n)).
  apply (exist _ (mod2 n)).
  split.
  - apply mod2_ok.
  - induction n using nat_2_ind; simpl.
    + repeat constructor.
    + repeat constructor.
    + assumption.
Defined.

(** [] *)


Fixpoint plus' (n m:nat){struct m} : nat :=
  match m with O => n | S p => S (plus' n p) 
  end.

Theorem plus'_O_n : forall n:nat, n=(plus' O n).
Proof.
 intros n; elim n; simpl; auto.
Qed.

Theorem plus'_Sn_m : forall n m:nat, S (plus' n m) = plus' (S n) m.
Proof.
 intros n m; elim m; simpl; auto.
Qed.

Theorem plus'_comm : forall n m:nat, plus' n m = plus' m n.
Proof.
 intros n m; elim m; simpl.
 apply plus'_O_n.
 intros p Hrec; rewrite <- plus'_Sn_m; auto.
Qed.

Theorem plus_plus' : forall n m:nat, n+m = plus' n m.
Proof.
 intros n m; rewrite plus'_comm; elim n; simpl; auto.
Qed.

Fixpoint plus'' (n m:nat){struct m} : nat :=
  match m with 0 => n | S p => plus'' (S n) p end.

Theorem plus''_Sn_m : forall n m:nat, S (plus'' n m) = plus'' (S n) m.
Proof.
 intros n m; elim m; simpl; auto.
 intros p Hrec.
 Restart.
 intros n m; generalize n; elim m; simpl.
 auto.
 intros p Hrec n0.
 trivial.
Qed.


(** Exercise 9.13 *)

Theorem plus'_assoc : forall n m o : nat,
  plus' (plus' n m) o = plus' n (plus' m o).
Proof.
  intros n m o. elim o.
  - reflexivity.
  - intros o' H.
    simpl. rewrite H. reflexivity.
Qed.

(** [] *)


(** Exercise 9.14 *)

Theorem plus''_assoc : forall n m o : nat,
  plus'' (plus'' n m) o = plus'' n (plus'' m o).
Proof.
  intros n m o. 
  generalize dependent m.
  generalize dependent n.
  induction o as [|o']; intros n m.
  - reflexivity.
  - simpl. 
    repeat rewrite <- plus''_Sn_m.
    rewrite (IHo' n m).
    simpl. rewrite <- plus''_Sn_m.
    reflexivity.
Qed.

(** [] *)


(** Exercise 9.15 *)

Fixpoint fib_aux (a b n : nat) : nat :=
  match n with
    | 0 => a
    | S p => fib_aux b (a+b) p
  end.

Definition fib_tr (n : nat) : nat :=
  fib_aux 1 1 n.

Lemma fib_aux_ssn : forall a b n : nat, 
  fib_aux a b (S (S n)) = fib_aux a b n + fib_aux a b (S n).
Proof.
  intros a b n.
  generalize dependent b.
  generalize dependent a.
  induction n.
  - reflexivity.
  - intros a b. simpl.
    apply (IHn b (a+b)).
Qed.

Theorem fib_tr_eq : forall n : nat, fib n = fib_tr n.
Proof.
  induction n using nat_fib_ind.
  - trivial.
  - trivial.
  - unfold fib_tr. 
    rewrite fib_aux_ssn.
    unfold fib_tr in *. 
    rewrite fib_ssn.
    rewrite IHn. rewrite IHn0.
    reflexivity.
Qed.
    
(** [] *)


Open Scope Z_scope.

Fixpoint div_bin (n m:positive){struct n} : Z*Z :=
 match n with
 | 1%positive => match m with 1%positive =>(1,0) | v =>(0,1) end
 | xO n' =>
   let (q',r'):=div_bin n' m in
   match Z_lt_ge_dec (2*r')(Zpos m) with
   | left Hlt => (2*q', 2*r')
   | right Hge => (2*q' + 1, 2*r' - (Zpos m))
   end
 | xI n' =>
   let (q',r'):=div_bin n' m in
   match Z_lt_ge_dec (2*r' + 1)(Zpos m) with
   | left Hlt => (2*q', 2*r' + 1)
   | right Hge => (2*q' + 1, (2*r' + 1)-(Zpos m))
   end
 end.


Theorem rem_1_1_interval : 0 <= 0 < 1.
Proof.
 omega.
Qed.

Theorem rem_1_even_interval : forall m:positive,  0 <= 1 < Zpos (xO m).
Proof.
 intros n'; split.
 auto with zarith.
 SearchPattern (1 < Zpos _).
 Locate "_ < _".
 compute.
 trivial.
Qed.

Theorem rem_1_odd_interval : forall m:positive, 0 <= 1 < Zpos (xI m).
Proof.
 split;[auto with zarith | compute; auto].
Qed.

Theorem rem_even_ge_interval :
 forall m r:Z, 0 <= r < m ->  2*r >= m -> 0 <= 2*r - m < m.
Proof.
 intros; omega.
Qed.

Theorem rem_even_lt_interval :
 forall m r:Z, 0 <= r < m -> 2*r < m -> 0 <= 2*r < m.
Proof.
 intros; omega.
Qed.

Theorem rem_odd_ge_interval :
 forall m r:Z, 0 <= r < m -> 2*r + 1 >= m -> 2*r + 1 - m <  m.
Proof.
 intros; omega.
Qed.

Theorem rem_odd_lt_interval :
 forall m r:Z, 0 <= r < m -> 2*r + 1 < m -> 0 <= 2*r + 1 < m.
Proof.
 intros; omega.
Qed.
Hint Resolve rem_odd_ge_interval rem_even_ge_interval
 rem_odd_lt_interval rem_even_lt_interval rem_1_odd_interval
 rem_1_even_interval rem_1_1_interval.

Ltac div_bin_tac arg1 arg2 :=
  elim arg1;
   [intros p; lazy beta iota delta [div_bin]; fold div_bin;
      case (div_bin p arg2); unfold snd; intros q' r' Hrec;
      case (Z_lt_ge_dec (2*r' + 1)(Zpos arg2)); intros H
   | intros p; lazy beta iota delta [div_bin]; fold div_bin;
      case (div_bin p arg2); unfold snd; intros q' r' Hrec;
      case (Z_lt_ge_dec (2*r')(Zpos arg2)); intros H
   | case arg2; lazy beta iota delta [div_bin]; intros].

Theorem div_bin_rem_lt :
 forall n m:positive, 0 <= snd (div_bin n m) < Zpos m.
Proof.
 intros n m; div_bin_tac n m; unfold snd; auto.
 omega.
Qed.

SearchRewrite (Zpos (xI _)).

SearchRewrite (Zpos (xO _)).


Theorem div_bin_eq :
 forall n m:positive,
   Zpos n =  (fst (div_bin n m))*(Zpos m) + snd (div_bin n m).
Proof.
 intros n m; div_bin_tac n m; 
  rewrite Zpos_xI || (try rewrite Zpos_xO);
  try rewrite Hrec; unfold fst, snd; ring.
Qed.

Inductive div_data (n m:positive) : Set :=
  div_data_def :
  forall q r:Z, Zpos n = q*(Zpos m)+r -> 0<= r < Zpos m -> div_data n m.

Definition div_bin2 : forall n m:positive, div_data n m.
 intros n m; elim n.
 intros n' [q r H_eq H_int].
 case (Z_lt_ge_dec (2*r + 1)(Zpos m)).
split with  (2*q) (2*r + 1).
 rewrite Zpos_xI; rewrite H_eq; ring.
 auto. 
split with  (2*q+1)(2*r + 1 - (Zpos m)).
 rewrite Zpos_xI; rewrite H_eq; ring.
 omega.
 intros n' [q r H_eq H_int].
 case (Z_lt_ge_dec (Zmult 2 r)(Zpos m)).
split with (Zmult 2 q)(Zmult 2 r).
 rewrite Zpos_xO; rewrite H_eq; ring.
 auto.
split with  (Zplus (Zmult 2 q) 1)(Zminus (Zmult 2 r)(Zpos m)).
 rewrite Zpos_xO; rewrite H_eq; ring.
 auto.
 case m.
split with  0%Z 1%Z.
 ring.
 auto.
split with  0%Z 1%Z.
 ring.
 auto.
split with  1%Z 0%Z.
 ring.
 auto.
Qed.

Definition div_bin3 : forall n m:positive, div_data n m.
 refine
  ((fix div_bin3 (n:positive) : forall m:positive, div_data n m :=
      fun m =>
        match n return div_data n m with
        | 1%positive =>
            match m return div_data 1 m with
            | 1%positive => div_data_def 1 1 1 0 _ _
            | xO p => div_data_def 1 (xO p) 0 1 _ _
            | xI p => div_data_def 1 (xI p) 0 1 _ _
            end
        | xO p =>
            match div_bin3 p m with
            | div_data_def _ _ q r H_eq H_int =>
                match Z_lt_ge_dec (Zmult 2 r)(Zpos m) with
                | left hlt =>
                    div_data_def (xO p) m (Zmult 2 q) 
                                 (Zmult 2 r) _ _
                | right hge =>
                    div_data_def (xO p) m (Zplus (Zmult 2 q) 1)
                      (Zminus (Zmult 2 r)(Zpos m)) _ _
                end
            end
        | xI p =>
            match div_bin3 p m with
            | div_data_def _ _ q r H_eq H_int =>
                match Z_lt_ge_dec (Zplus (Zmult 2 r) 1)(Zpos m) 
                with
                | left hlt =>
                    div_data_def (xI p) m (Zmult 2 q)
                      (Zplus (Zmult 2 r) 1) _ _
                | right hge =>
                    div_data_def (xI p) m (Zplus (Zmult 2 q) 1)
                      (Zminus (Zplus (Zmult 2 r) 1)(Zpos m)) _ _
                end
            end
        end)); 
      clear div_bin3; try rewrite Zpos_xI; try rewrite Zpos_xO;
      try rewrite H_eq; auto with zarith; try (ring; fail).
 split;[auto with zarith | compute; auto].
 split;[auto with zarith | compute; auto].
Defined.

