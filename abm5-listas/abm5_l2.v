Require Export abm5_l1.


(* The following line is usually necessary if you are working with files in Coq.
   Since we are providing all in one block, it's commented out here.
   But in a real Coq environment, you'd need to make sure all dependencies are properly required. *)
(* From LF Require Export Basics. *)

Theorem plus_n_O : forall n:nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite <- IHn'. reflexivity. Qed.

Theorem minus_n_n : forall n,
  minus n n = 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) simpl. reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) simpl. reflexivity.
  - (* n = S n' *) simpl. rewrite IHn'. reflexivity. Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m. induction n as [| n' IHn'].
  - (* n = 0 *) simpl. reflexivity.
  - (* n = S n' *) simpl. rewrite IHn'. reflexivity. Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m. induction n as [| n' IHn'].
  - (* n = 0 *) simpl. rewrite <- plus_n_O. reflexivity.
  - (* n = S n' *) simpl. rewrite IHn'. rewrite plus_n_Sm. reflexivity. Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  - (* n = 0 *) simpl. reflexivity.
  - (* n = S n' *) simpl. rewrite IHn'. reflexivity. Qed.

(* Exercise: 2 stars, standard (double_plus *)

Lemma double_plus : forall n, double n = n + n.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* Base case: n = 0 *)
    simpl. reflexivity.
  - (* Inductive step: n = S n' *)
    simpl. rewrite -> IHn'. rewrite <- plus_n_Sm. reflexivity.
Qed.

(* Exercise: 2 stars, standard, optional (evenb_S) *)

(* Definition of evenb *)
Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

(* Definition of negb *)
Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

(* Theorem proving evenb (S n) = negb (evenb n) *)
Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof.
  intros n. induction n as [| n' IHn'].
  - (* Base case: n = 0 *)
    simpl. reflexivity.
  - (* Inductive step: n = S n' *)
    rewrite IHn'. simpl.
    destruct (evenb n') eqn:E.
    + simpl. reflexivity.
    + simpl. reflexivity.
Qed.

(* Exercise: 3 stars, standard, especially useful (mult_comm *)

(* Definitions for plus and mult, typically found in the Basics chapter *)
Fixpoint plus (n m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Fixpoint mult (n m : nat) : nat :=
  match n with
  | O => O
  | S n' => plus m (mult n' m)
  end.

Notation "x + y" := (plus x y) (at level 50, left associativity).
Notation "x * y" := (mult x y) (at level 40, left associativity).

(* Theorems about addition that are typically proven in the Basics chapter *)
Theorem plus_n_O : forall n:nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m. induction n as [| n' IHn'].
  - simpl. rewrite <- plus_n_O. reflexivity.
  - simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

(* Theorem plus_swap *)
Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  assert (H: n + m = m + n).
  { rewrite -> plus_comm. reflexivity. }
  rewrite -> plus_assoc.
  rewrite -> H.
  rewrite <- plus_assoc.
  assert (H2: m + p = p + m).
  { rewrite -> plus_comm. reflexivity. }
  rewrite -> H2.
  reflexivity.
Qed.

(* Helper lemma for distributivity of multiplication over addition *)
Lemma mult_n_Sm : forall n m : nat,
  n * (S m) = n + (n * m).
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. rewrite -> plus_swap. reflexivity.
Qed.

(* Theorem mult_0_r, typically proven in the Basics chapter *)
Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

(* Proof of multiplication commutativity *)
Theorem mult_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros m n.
  induction n as [| n' IHn'].
  - simpl. rewrite <- mult_0_r. reflexivity.
  - simpl. rewrite -> IHn'. rewrite -> mult_n_Sm. rewrite -> plus_comm. reflexivity.
Qed.

(* Exercise: 3 stars, standard, optional (more_exercises *)

(* Theorems about less than or equal to, and equality checks for natural numbers *)
Require Import Arith.

Theorem leb_refl : forall n:nat,
  true = (n <=? n).
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem zero_nbeq_S : forall n:nat,
  0 =? (S n) = false.
Proof.
  intros n. simpl. reflexivity.
Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  intros b. destruct b.
  - reflexivity.
  - reflexivity.
Qed.

Theorem plus_ble_compat_l : forall n m p : nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
  intros n m p H. induction p as [| p' IHp'].
  - simpl. apply H.
  - simpl. apply IHp'.
Qed.

Theorem S_nbeq_0 : forall n:nat,
  (S n) =? 0 = false.
Proof.
  intros n. simpl. reflexivity.
Qed.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  intros n. simpl. rewrite <- plus_n_O. reflexivity.
Qed.

Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
Proof.
  intros b c. destruct b.
  - destruct c.
    + reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. rewrite plus_assoc. reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. rewrite mult_plus_distr_r. reflexivity.
Qed.
