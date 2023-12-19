(* Exercise: 2 stars, standard (and_exercise) *)
Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m H.         (* Introduce n, m, and assumption H *)
  split.                (* Split into two subgoals: n = 0 and m = 0 *)
  - destruct n as [|n'].
    + reflexivity.     (* Case n = 0, directly proven *)
    + inversion H.     (* Case n = S n', derive a contradiction from H *)
  - destruct n as [|n'].
    + simpl in H. apply H. (* Case n = 0, use H to prove m = 0 *)
    + inversion H.         (* Case n = S n', derive a contradiction from H *)
Qed.


(* Exercise: 2 stars, standard (and_assoc) *)
Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].  (* Introduce P, Q, R and decompose the hypothesis *)
  split.                     (* Split the goal into two subgoals *)
  - split.                   (* Split the first subgoal (P /\ Q) *)
    + apply HP.              (* Prove P *)
    + apply HQ.              (* Prove Q *)
  - apply HR.                (* Prove R *)
Qed.


(* Exercise: 2 stars, standard, especially useful (contrapositive) *)
Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H.       (* Introduce P, Q, and assumption H: P -> Q *)
  intros NQ.          (* Introduce assumption NQ: ~Q *)
  unfold not.         (* Unfold the definition of not (~) *)
  intros HP.          (* Assume P *)
  apply NQ.           (* Use assumption NQ to derive a contradiction *)
  apply H.            (* Apply H to derive Q from P *)
  apply HP.           (* Apply HP to conclude the proof *)
Qed.


(* Exercise: 1 star, standard (not_both_true_and_false) *)
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  intros P.                (* Introduce P *)
  unfold not.              (* Unfold the definition of not *)
  intros [HP HNP].         (* Introduce the contradictory assumption and destruct it *)
  apply HNP.               (* Apply HNP to derive a contradiction *)
  apply HP.                (* Apply HP *)
Qed.


(* Exercise: 3 stars, standard (or_distributes_over_and) *)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.          (* Introduce P, Q, R *)
  split.                 (* Split into forward and reverse directions *)

  - (* Forward Direction *)
    intros H.            (* Introduce assumption H: P \/ (Q /\ R) *)
    destruct H as [HP | [HQ HR]]. (* Destruct H into two cases *)
    + split; left; apply HP. (* Case P: Both subgoals can be proven by left disjunction with P *)
    + split; right; [apply HQ | apply HR]. (* Case Q /\ R: Split into two subgoals and apply HQ and HR *)

  - (* Reverse Direction *)
    intros [H1 H2].      (* Introduce assumption H: (P \/ Q) /\ (P \/ R) and destruct it *)
    destruct H1 as [HP | HQ]; destruct H2 as [HP' | HR].
    + left; apply HP.   (* Case P, P: P suffices to prove the goal *)
    + left; apply HP.   (* Case P, R: P suffices to prove the goal *)
    + left; apply HP'.  (* Case Q, P: P suffices to prove the goal *)
    + right; split; [apply HQ | apply HR]. (* Case Q, R: Construct the conjunction Q /\ R *)
Qed.


(* Exercise: 1 star, standard, especially useful (dist_not_exists) *)
Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X P H.      (* Introduce X, P, and assumption H *)
  unfold not.        (* Unfold the definition of not *)
  intros [x NPx].    (* Introduce the contrary assumption and destruct it *)
  apply NPx.         (* Apply NPx to derive a contradiction *)
  apply H.           (* Apply H to get P x *)
  apply x.           (* Apply x to conclude the proof *)
Qed.


(* Exercise: 2 stars, standard (dist_exists_or) *)
Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q.        (* Introduce X, P, Q *)
  split.               (* Split into forward and reverse directions *)

  - (* Forward Direction *)
    intros [x [HP | HQ]]. (* Introduce the existential quantifier and destruct the disjunction *)
    + left. exists x. apply HP.  (* Construct (exists x, P x) *)
    + right. exists x. apply HQ. (* Construct (exists x, Q x) *)

  - (* Reverse Direction *)
    intros [H | H];     (* Destruct the disjunction in H *)
    destruct H as [x H]; (* Destruct the existential quantifier in H *)
    exists x;           (* Construct the existential quantifier for the result *)
    [left | right];     (* Construct the disjunction for the result *)
    apply H.            (* Apply the hypothesis H *)
Qed.


(* Exercise: 3 stars, standard (In_map_iff) *)
Theorem In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
    exists x, f x = y /\ In x l.
Proof.
  intros A B f l y. split.
  
  - (* Forward Direction *)
    induction l as [|x l' IHl'].
    + (* l = [] *) simpl. intros []. (* This case is vacuously true, as an empty list yields no elements *)
    + (* l = x :: l' *) simpl. intros [H | H].
      * (* y = f x *) exists x. split; [apply H | left; reflexivity].
      * (* y in map f l' *) apply IHl' in H. destruct H as [x' [H1 H2]]. exists x'. split; [apply H1 | right; apply H2].

  - (* Reverse Direction *)
    intros [x [H1 H2]]. (* Introduce the existential quantifier and destruct the conjunction *)
    rewrite in_map_iff. (* Apply the in_map_iff lemma *)
    exists x. split; [apply H2 | apply H1]. (* Construct the existential quantifier and split the conjunction *)
Qed.


(* Exercise: 2 stars, standard (In_app_iff) *)
Theorem In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros A l. induction l as [|a' l' IH].
  
  - (* Base case: l = [] *)
    simpl. intros a. split.
    + (* Forward Direction *) intros H. right. apply H.
    + (* Reverse Direction *) intros [H | H]; [contradiction | apply H].

  - (* Inductive case: l = a' :: l' *)
    simpl. intros a. split.
    + (* Forward Direction *) intros [H | H].
      * (* a is the head of l *) left. left. apply H.
      * (* a is in the tail of l or in l' *) apply IH in H. destruct H as [H | H]; [left; right; apply H | right; apply H].
    + (* Reverse Direction *) intros [H | H].
      * (* a is in l *) destruct H as [H | H]; [left; apply H | right; apply IH; left; apply H].
      * (* a is in l' *) right; apply IH; right; apply H.
Qed.


(* Exercise: 3 stars, standard, especially useful (All) *)
Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | [] => True
  | x :: l' => P x /\ All P l'
  end.

Theorem All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
  intros T P l. split.
  - (* Forward Direction *)
    induction l as [|x l' IH].
    + (* l = [] *) simpl. intros _. apply I.
    + (* l = x :: l' *) simpl. intros H. split.
      * (* Head *) apply H. left. reflexivity.
      * (* Tail *) apply IH. intros y Hy. apply H. right. apply Hy.
  - (* Reverse Direction *)
    induction l as [|x l' IH].
    + (* l = [] *) simpl. intros _ y Hy. inversion Hy.
    + (* l = x :: l' *) simpl. intros [Hx Hl'] y Hy. destruct Hy as [Hy | Hy].
      * (* y = x *) rewrite <- Hy. apply Hx.
      * (* y in l' *) apply IH. apply Hl'. apply Hy.
Qed.


(* Exercise: 4 stars, standard (tr_rev_correct) *)
Require Import Coq.Lists.List.
Import ListNotations.

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

(* Proof of the correctness of rev_append *)
Lemma rev_append_correct : forall (X : Type) (l1 l2 : list X),
    rev_append l1 l2 = rev l1 ++ l2.
Proof.
  intros X l1 l2. induction l1 as [| x l1' IH].
  - simpl. reflexivity.
  - simpl. rewrite <- IH. rewrite <- app_assoc. reflexivity.
Qed.

(* Proof of tr_rev_correct *)
Theorem tr_rev_correct : forall (X : Type), @tr_rev X = @rev X.
Proof.
  intros X. unfold tr_rev. apply functional_extensionality. intros l.
  rewrite rev_append_correct. rewrite app_nil_r. reflexivity.
Qed.


(* Exercise: 3 stars, standard (evenb_double_conv) *)
Require Import Coq.Arith.Even.
Require Import Coq.Arith.Double.

Lemma evenb_double_conv : forall n, exists k,
  n = if evenb n then double k else S (double k).
Proof.
  intros n.
  induction n as [|n' IH].
  - (* n = 0 *)
    exists 0. simpl. reflexivity.
  - (* n = S n' *)
    destruct IH as [k IH].
    exists (if evenb n' then S k else k).
    destruct (evenb n') eqn:En'.
    + (* n' is even *)
      rewrite IH. simpl. rewrite <- double_S. reflexivity.
    + (* n' is odd *)
      rewrite IH. simpl. reflexivity.
Qed.


(* Exercise: 2 stars, standard (logical_connectives) *)
Theorem andb_true_iff : forall b1 b2:bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  intros b1 b2. split.
  - (* Forward Direction *)
    intros H. split.
    + destruct b1.
      * reflexivity.
      * simpl in H. contradiction.
    + destruct b2.
      * reflexivity.
      * rewrite andb_false_r in H. contradiction.
  - (* Reverse Direction *)
    intros [H1 H2]. rewrite H1. rewrite H2. reflexivity.
Qed.

Theorem orb_true_iff : forall b1 b2,
  b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
  intros b1 b2. split.
  - (* Forward Direction *)
    intros H. destruct b1.
    + left. reflexivity.
    + right. simpl in H. apply H.
  - (* Reverse Direction *)
    intros [H | H].
    + rewrite H. reflexivity.
    + rewrite H. destruct b1; reflexivity.
Qed.


(* Exercise: 1 star, standard (eqb_neq) *)
Theorem eqb_neq : forall x y : nat,
  x =? y = false <-> x <> y.
Proof.
  intros x y. split.
  - (* Forward Direction *)
    intros H. unfold not. intros Hxy. rewrite Hxy in H. rewrite Nat.eqb_refl in H. discriminate H.
  - (* Reverse Direction *)
    unfold not. intros H. destruct (x =? y) eqn:Hxy.
    + (* Case: x =? y = true *)
      apply Nat.eqb_eq in Hxy. contradiction.
    + (* Case: x =? y = false *)
      reflexivity.
Qed.


(* Exercise: 3 stars, standard (eqb_list) *)
Fixpoint eqb_list {A : Type} (eqb : A -> A -> bool)
                  (l1 l2 : list A) : bool :=
  match l1, l2 with
  | [], [] => true
  | a1 :: l1', a2 :: l2' => eqb a1 a2 && eqb_list eqb l1' l2'
  | _, _ => false
  end.


Theorem eqb_list_true_iff :
  forall A (eqb : A -> A -> bool),
    (forall a1 a2, eqb a1 a2 = true <-> a1 = a2) ->
    forall l1 l2, eqb_list eqb l1 l2 = true <-> l1 = l2.
Proof.
  intros A eqb H l1 l2. split.
  - (* Forward Direction *)
    generalize dependent l2.
    induction l1 as [|a1 l1' IH]; intros l2.
    + destruct l2.
      * reflexivity.
      * simpl. intros Hfalse. discriminate Hfalse.
    + destruct l2 as [|a2 l2'].
      * simpl. intros Hfalse. discriminate Hfalse.
      * simpl. intros Heqb. apply andb_true_iff in Heqb. destruct Heqb as [Heq1 Heq2].
        apply H in Heq1. apply IH in Heq2. rewrite Heq1, Heq2. reflexivity.
  - (* Reverse Direction *)
    intros Hl. rewrite Hl. clear Hl.
    induction l1 as [|a1 l1' IH].
    + reflexivity.
    + simpl. rewrite H. rewrite IH. reflexivity.
Qed.


(* Exercise: 2 stars, standard, especially useful (All_forallb) *)
Theorem forallb_true_iff : forall X test (l : list X),
   forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  intros X test l. split.
  - (* Forward Direction *)
    induction l as [|x l' IH].
    + (* l = [] *) intros _. simpl. apply I.
    + (* l = x :: l' *) simpl. intros H. apply andb_true_iff in H. destruct H as [Hx Hl'].
      split.
      * (* Head *) apply Hx.
      * (* Tail *) apply IH. apply Hl'.
  - (* Reverse Direction *)
    induction l as [|x l' IH].
    + (* l = [] *) simpl. reflexivity.
    + (* l = x :: l' *) simpl. intros [Hx Hl']. apply andb_true_iff. split.
      * (* Head *) apply Hx.
      * (* Tail *) apply IH. apply Hl'.
Qed.


(* Exercise: 3 stars, standard (excluded_middle_irrefutable) *)
Theorem excluded_middle_irrefutable: forall (P:Prop),
  ~ ~ (P \/ ~ P).
Proof.
  intros P H. apply H.
  right. intros HP. apply H.
  left. apply HP.
Qed.

