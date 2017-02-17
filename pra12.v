Inductive bool : Type := 
  | true : bool
  | false : bool.

Definition negb (b:bool) : bool := 
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool := 
  match b1 with 
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool := 
  match b1 with 
  | true => true
  | false => b2
  end.

Definition nandb (b1:bool) (b2:bool) : bool := 
  match b1 with
  | false => true
  | true => negb b2
  end.

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3 : (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) :bool := 
  match b1 with
  | false => false
  | true => andb b2 b3
  end.

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Admitted.
Example test_andb34: (andb3 true true false) = false.
Admitted.

Module Playground1.

Inductive nat : Type := 
  | O : nat
  | S : nat -> nat.

Definition pred (n : nat) : nat := 
  match n with
    | O => O
    | S nn => nn
  end.

End Playground1.

Definition minustwo (n: nat) : nat := 
  match n with
    | O => O
    | S O => O
    | S (S nn) => nn
  end.

Check (S (S (S (S O)))).
Eval simpl in (minustwo 4).
Check minustwo.
Check S.
Check pred.

Fixpoint evenb (n:nat) : bool := 
  match n with
  | O => true
  | S O => false
  | S (S nn) => evenb nn
  end.

Module Playground2.

Fixpoint plux (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S nn => S (plus nn m)
  end.

Eval simpl in plus (S (S (S O))) (S (S O)).

Fixpoint mult (n m : nat) :nat := 
  match n with
    | O => O
    | S nn => plus m (mult nn m)
  end.

Fixpoint minus (n m:nat) : nat := 
  match n, m with
    | O, _ => O
    | S _ , O => n
    | S nn, S mm => minus nn mm
  end.

End Playground2.


Fixpoint factorial (n:nat) : nat := 
  match n with
    | O => S O
    | S nn => mult (n) (factorial nn)
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Notation "x + y" :=
  (plus x y) (at level 50, left associativity) : nat_scope.
Notation "x - y" :=
  (minus x y) (at level 50, left associativity) : nat_scope.
Notation "x * y" := 
  (mult x y) (at level 40, left associativity) : nat_scope.

Check ((0 + 1) + 1).

Fixpoint beq_nat (n m : nat) : bool := 
  match n with
  | O => match m with
        | O => true
        | S mm => false
        end
  | S nn => match m with
            | O => false
            | S mm => beq_nat nn mm
            end
  end.


Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S nn =>
    match m with
    | O => false
    | S mm => ble_nat nn mm
    end
  end.

Example test_ble_nat1: (ble_nat 2 2) = true.
Proof. simpl. reflexivity. Qed.
Example test_ble_nat2: (ble_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_ble_nat3: (ble_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.


Eval simpl in beq_nat 2 2.

Definition blt_nat (n m : nat) :=
  andb (ble_nat n m) (negb (beq_nat n m)).


Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. compute. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. compute. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.


Theorem plus_0_n : forall n:nat, 0+n = n.
Proof.
  reflexivity. Qed.

Eval simpl in (forall n:nat, n + 0 = n).
Eval simpl in (forall n:nat, 0 + n = n).

Theorem plus_0_n'' : forall n:nat, 0+n = n.
Proof.
  intros n.
  reflexivity.
  Qed.

Theorem plus_1_l : forall n:nat, 1+n = S n.
Proof.
  intros n. reflexivity. Qed.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intros n. reflexivity. Qed.

Theorem plus_id_example : forall n m: nat,
  n = m -> n+n = m+m.
Proof.
  intros n m.
  intros H.
  rewrite <- H.
  reflexivity.
  Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n+m = m+o.
Proof.
  intros n m o.
  intros.
  rewrite -> H.
  rewrite -> H0.
  reflexivity.
Qed.


Theorem mult_0_plus : forall n m : nat,
  (0+n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_0_n.
  reflexivity.
Qed.

Theorem mult_1_plus : forall n m : nat,
  (1+n) * m = m + (n*m).
Proof.
  intros.
  reflexivity.
Qed.


Theorem plus_1_neq_0_firsttry : forall n : nat,
  beq_nat (n+1) 0 = false.
Proof.
  intros n. 
  destruct n as [| nn].
  reflexivity.
  reflexivity.
Qed.

Theorem neg_involutiv : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b.
  reflexivity.
  reflexivity. Qed.


Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n+1) = false.
  Proof.
    intros.
    destruct n as [| nn].
    reflexivity.
    reflexivity.
  Qed.


Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.


Theorem andb_true_elim1 : forall b c : bool,
  andb b c = true -> b = true.
Proof.
  intros b c H.
  destruct b.
  Case "b = true".
    reflexivity.
  Case "b = false".
    rewrite <- H. reflexivity. Qed.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
  Proof.
    intros.
    destruct c.
    Case "c = true".
      reflexivity.
    Case "c = false".
      rewrite <- H.
      destruct b.
      reflexivity.
      reflexivity.
  Qed.

Theorem plus_0_r : forall n:nat,
n+0 = n.
Proof.
  intros n. induction n as [| nn].
  Case "n = 0". reflexivity.
  Case "n = S nn".
    simpl.
    rewrite -> IHnn.
    reflexivity.
Qed.

Theorem mult_0_r : forall n:nat,
  n*0 = 0.
Proof.
  intros.
  induction n as [| nn].
  Case "n = 0".
    reflexivity.
  Case "n = S nn".
    simpl.
    rewrite -> IHnn.
    reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n+m) = n+(S m).
Proof.
  intros.
  induction n as [| nn].
  Case "n = 0".
    simpl.
    reflexivity.
  Case "n = S nn".
    simpl.
    rewrite -> IHnn.
    reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros.
  induction n.
  simpl.
  rewrite -> plus_0_r.
  reflexivity.
  simpl.
  rewrite -> IHn.
  rewrite -> plus_n_Sm.
  reflexivity.
Qed.

Fixpoint double (n:nat) := 
  match n with
  | O => O
  | S nn => S(S (double nn))
  end.

Lemma double_plus : forall n, double n = n+n.
Proof.
  intros.
  induction n.
  Case "n = 0".
    simpl.
    reflexivity.
  Case "n = S n".
    simpl.
    rewrite -> IHn.
    rewrite <- plus_n_Sm.
    reflexivity.
Qed.


