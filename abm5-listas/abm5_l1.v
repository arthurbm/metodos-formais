(* Exercise: 1 star, standard (nandb) *)

Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1, b2 with
  | true, true => false
  | _, _ => true
  end.

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

(* Exercise: 1 star, standard (andb3) *)

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1, b2, b3 with
  | true, true, true => true
  | _, _, _ => false
  end.

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.

Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.

Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.

Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

(* Exercise: 1 star, standard (factorial) *)

Fixpoint factorial (n:nat) : nat :=
  match n with
  | O => 1
  | S n' => n * factorial n'
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.

Example test_factorial2: (factorial 5) = (10 * 12).
Proof. simpl. reflexivity. Qed.


(* Exercise: 1 star, standard (ltb) *)

Definition ltb (n m : nat) : bool := negb (n >=? m).

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Example test_ltb1: (2 <? 2) = false.
Proof. simpl. reflexivity. Qed.

Example test_ltb2: (2 <? 4) = true.
Proof. simpl. reflexivity. Qed.

Example test_ltb3: (4 <? 2) = false.
Proof. simpl. reflexivity. Qed.


(* Exercise: 1 star, standard (plus_id_exercise) *)

Theorem plus_id_exercise : ∀ n m o : nat,
  n = m → m = o → n + m = m + o.
Proof.
  intros n m o.
  intros Hnm Hmo.
  rewrite -> Hnm.
  rewrite <- Hmo.
  reflexivity. Qed.


(* Exercise: 1 star, standard (mult_n_1) *)

Theorem mult_n_1 : ∀ p : nat,
  p * 1 = p.
Proof.
  intros p.
  rewrite <- mult_n_Sm with (n := p) (m := 0).
  simpl.
  rewrite <- mult_n_O with (n := p).
  reflexivity. Qed.



(* Exercise: 2 stars, standard (andb_true_elim2) *)

Theorem andb_true_elim2 : ∀ b c : bool,
  andb b c = true → c = true.
Proof.
  intros b c H. (* Introduce b, c, and hypothesis H *)
  destruct b eqn:Eb. (* Case analysis on b *)
  - (* Case b = true *)
    simpl in H. (* Simplify andb true c in hypothesis H *)
    apply H. (* H is now "c = true", which is what we need to prove *)
  - (* Case b = false *)
    simpl in H. (* Simplify andb false c in hypothesis H, which simplifies to false *)
    rewrite H. (* This will replace c with true, because "false = true" is impossible *)
    reflexivity.
Qed.

(* Exercise: 1 star, standard (zero_nbeq_plus_1) *)

Theorem zero_nbeq_plus_1 : ∀ n : nat,
  0 =? (n + 1) = false.
Proof.
  intros n. (* Introduce the variable n *)
  destruct n as [|n'] eqn:En. (* Perform case analysis on n *)
  - (* Case n = 0 *)
    reflexivity. (* Simplifies to "0 =? 1 = false" which is trivially true by definition of =? *)
  - (* Case n = S n' for some n' *)
    reflexivity. (* Simplifies to "0 =? (S n' + 1) = false" which is also trivially true as S n' + 1 will never be 0 *)
Qed.

(* Exercise: 1 star, standard (identity_fn_applied_twice) *)

Theorem identity_fn_applied_twice :
  ∀ (f : bool → bool),
  (∀ (x : bool), f x = x) →
  ∀ (b : bool), f (f b) = b.
Proof.
  intros f H b. (* Introduce the function f, its property H, and the boolean b *)
  rewrite H. (* Use the property H to rewrite f b to b *)
  rewrite H. (* Use the property H again to rewrite f b to b *)
  reflexivity. (* Now we have b = b, which is trivially true *)
Qed.


(* Exercise: 3 stars, standard (binary) *)

Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).

Fixpoint incr (m:bin) : bin :=
  match m with
  | Z => B1 Z                  (* incrementing zero gives one *)
  | B0 m' => B1 m'             (* a zero becomes a one *)
  | B1 m' => B0 (incr m')      (* a one becomes a zero, and we carry over the increment *)
  end.

Fixpoint bin_to_nat (m:bin) : nat :=
  match m with
  | Z => O
  | B0 m' => 2 * (bin_to_nat m')  (* a zero at the end means double the number *)
  | B1 m' => S (2 * (bin_to_nat m'))  (* a one at the end means double, plus one *)
  end.

Example test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z).
Proof. reflexivity. Qed.

Example test_bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z).
Proof. reflexivity. Qed.

Example test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)).
Proof. reflexivity. Qed.

Example test_bin_incr4 : bin_to_nat (B0 (B1 Z)) = 2.
Proof. reflexivity. Qed.

Example test_bin_incr5 : bin_to_nat (incr (B1 Z)) = 1 + bin_to_nat (B1 Z).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr6 : bin_to_nat (incr (incr (B1 Z))) = 2 + bin_to_nat (B1 Z).
Proof. simpl. reflexivity. Qed.
