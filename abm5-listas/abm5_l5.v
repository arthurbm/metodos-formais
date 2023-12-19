(* Exercise: 3 stars, standard (apply_exercise1) *)
Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
  intros l l' H.       (* Step 1 *)
  rewrite <- H.        (* Step 2 *)
  apply rev_involutive. (* Step 3 *)
Qed.


(* Exercise: 3 stars, standard, optional (trans_eq_exercise) *)
Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  intros n m o p H1 H2.   (* Step 1: Introduce variables and hypotheses *)
  rewrite <- H1 in H2.   (* Use the first hypothesis to rewrite the second *)
  apply H2.             (* Apply the modified second hypothesis to conclude the proof *)
Qed.


(* Exercise: 3 stars, standard (injection_ex3) *)
Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  j = z :: l ->
  x = y.
Proof.
  intros X x y z l j H1 H2.   (* Step 1 *)
  injection H1 as Hx Hz.    (* Step 2 *)
  rewrite H2 in Hz.         (* Step 3 *)
  injection Hz as Hy.       (* Step 4 *)
  rewrite <- Hx in Hy.      (* Step 5 *)
  apply Hy.                 (* Step 5 & 6 *)
Qed.


(* Exercise: 1 star, standard (discriminate_ex3) *)
Example discriminate_ex3 :
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] ->
    x = z.
Proof.
  intros X x y z l j H.   (* Step 1 *)
  discriminate H.         (* Step 2 *)
Qed.


(* Exercise: 2 stars, standard (eqb_true) *)
Theorem eqb_true : forall n m,
    n =? m = true -> n = m.
Proof.
  intros n m.           (* Introduce n and m *)
  generalize dependent m. (* Allow m to vary during induction *)
  induction n as [| n' IHn'].
  - (* Base case: n = 0 *)
    intros m H. destruct m as [| m'].
    + reflexivity.     (* Case m = 0 *)
    + simpl in H. discriminate H. (* Case m = n + 1, which leads to a contradiction *)
  - (* Inductive step: n = n' + 1 *)
    intros m H. destruct m as [| m'].
    + simpl in H. discriminate H. (* Case m = 0, which leads to a contradiction *)
    + simpl in H. apply IHn' in H. rewrite H. reflexivity.
Qed.


(* Exercise: 3 stars, standard, especially useful (plus_n_n_injective) *)
Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n. induction n as [| n' IH].
  - (* Base case: n = 0 *)
    intros m H. simpl in H. 
    destruct m as [| m'].
    + reflexivity.
    + discriminate H.
  - (* Inductive step: n = S n' *)
    intros m H. destruct m as [| m'].
    + discriminate H.
    + apply f_equal. apply IH. simpl in H. 
      injection H as H'. apply plus_n_Sm in H'. simpl in H'. 
      apply H'.
Qed.


(* Exercise: 3 stars, standard, especially useful (gen_dep_practice) *)
Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     nth_error l n = None.
Proof.
  intros n X l. generalize dependent n. (* Allow n to vary during induction *)
  induction l as [| x l' IHl'].
  - (* Base case: l = [] *)
    intros n H. simpl in H. rewrite <- H. reflexivity.
  - (* Inductive step: l = x :: l' *)
    intros n H. destruct n as [| n'].
    + simpl in H. discriminate H.
    + simpl. apply IHl'. simpl in H. injection H as H'. apply H'.
Qed.


(* Exercise: 3 stars, standard (combine_split) *)
Require Import Coq.Lists.List.
Import ListNotations.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y) : list (X*Y) :=
  match lx, ly with
  | x::tx, y::ty => (x,y) :: (combine tx ty)
  | _, _ => []
  end.

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l. induction l as [| [x y] t IH].
  - (* Base case: l = [] *)
    intros l1 l2 H. simpl in H. injection H as H1 H2. rewrite <- H1, <- H2. reflexivity.
  - (* Inductive step: l = (x, y) :: t *)
    intros l1 l2 H. simpl in H. 
    destruct (split t) as [lx ly].
    injection H as H1 H2. simpl. rewrite <- H1, <- H2.
    rewrite IH. reflexivity.
Qed.


(* Exercise: 2 stars, standard (destruct_eqn_practice) *)
Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros f b. 
  destruct b.
  - (* Case b = true *)
    destruct (f true) eqn:Ft.
    + rewrite Ft. apply Ft.
    + destruct (f false) eqn:Ff.
      * apply Ft.
      * apply Ff.
  - (* Case b = false *)
    destruct (f false) eqn:Ff.
    + destruct (f true) eqn:Ft.
      * apply Ft.
      * apply Ff.
    + rewrite Ff. apply Ff.
Qed.


(* Exercise: 3 stars, standard (eqb_sym) *)
Theorem eqb_sym : forall (n m : nat),
  (n =? m) = (m =? n).
Proof.
  intros n. induction n as [| n' IH].
  - (* Base case: n = 0 *)
    intros m. destruct m as [| m'].
    + reflexivity.  (* Both are 0 *)
    + reflexivity.  (* 0 =? S m' is false, as is S m' =? 0 *)
  - (* Inductive step: n = S n' *)
    intros m. destruct m as [| m'].
    + reflexivity.  (* S n' =? 0 is false, as is 0 =? S n' *)
    + simpl. apply IH.  (* Apply the inductive hypothesis *)
Qed.

