Require Export SfLib_J.

Module AExp.

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

Fixpoint aeval (e : aexp) : nat :=
  match e with
  | ANum n => n
  | APlus a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2  => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

Example test_aeval1:
  aeval (APlus (ANum 2) (ANum 2)) = 4.
Proof. reflexivity. Qed.

Fixpoint beval (e : bexp) : bool :=
  match e with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => beq_nat (aeval a1) (aeval a2)
  | BLe a1 a2 => ble_nat (aeval a1) (aeval a2)
  | BNot b1 => negb (beval b1)
  | BAnd b1 b2 => andb (beval b1) (beval b2)
  end.

Fixpoint optimize_0plus (e:aexp) : aexp :=
  match e with
  | ANum n =>
      ANum n
  | APlus (ANum 0) e2 =>
      optimize_0plus e2
  | APlus e1 e2 =>
      APlus (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 =>
      AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult e1 e2 =>
      AMult (optimize_0plus e1) (optimize_0plus e2)
  end.

Example test_optimize_0plus:
  optimize_0plus (APlus (ANum 2)
                        (APlus (ANum 0)
                               (APlus (ANum 0) (ANum 1))))
  = APlus (ANum 2) (ANum 1).
Proof. reflexivity. Qed.

Theorem optimize_0plus_sound: forall e,
  aeval (optimize_0plus e) = aeval e.
Proof.
  intros e. induction e.
  Case "ANum". reflexivity.
  Case "APlus". destruct e1.
    SCase "e1 = ANum n". destruct n.
      SSCase "n = 0".  simpl. apply IHe2.
      SSCase "n <> 0". simpl. rewrite IHe2. reflexivity.
    SCase "e1 = APlus e1_1 e1_2".
      simpl. simpl in IHe1. rewrite IHe1.
      rewrite IHe2. reflexivity.
    SCase "e1 = AMinus e1_1 e1_2".
      simpl. simpl in IHe1. rewrite IHe1.
      rewrite IHe2. reflexivity.
    SCase "e1 = AMult e1_1 e1_2".
      simpl. simpl in IHe1. rewrite IHe1.
      rewrite IHe2. reflexivity.
  Case "AMinus".
    simpl. rewrite IHe1. rewrite IHe2. reflexivity.
  Case "AMult".
    simpl. rewrite IHe1. rewrite IHe2. reflexivity.  Qed.

Lemma foo : forall n, ble_nat 0 n = true.
Proof.
  intros.
  destruct n.

    Case "n=0". simpl. reflexivity.
    Case "n=Sn'". simpl. reflexivity.

Qed.

Lemma foo' : forall n, ble_nat 0 n = true.
Proof.
  intros.

  destruct n;

  simpl;

  reflexivity.
Qed.

Theorem optimize_0plus_sound':forall e,
  aeval (optimize_0plus e) = aeval e.
Proof.
  intros e.
  induction e;
  
  try(simpl;rewrite IHe1; rewrite IHe2;reflexivity).
  
  Case "Anum". reflexivity.
  
  Case "APlus".
    destruct e1; try (simpl; simpl in IHe1; rewrite IHe1; rewrite IHe2; reflexivity).
    SCase "e1 = ANum n". destruct n;
      simpl; rewrite IHe2;reflexivity.
Qed.

Tactic Notation "simpl_and_try" tactic(c) :=
  simpl;
  try c.

Tactic Notation "aexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ANum" | Case_aux c "APlus"
  | Case_aux c "AMinus" | Case_aux c "AMult"].

Theorem optimize_0plus_sound''': forall e,
  aeval (optimize_0plus e) = aeval e.
Proof.
  intros e.
  aexp_cases (induction e) Case;
    try (simpl; rewrite IHe1; rewrite IHe2; reflexivity);
    try reflexivity.
  Case "APlus".
    aexp_cases (destruct e1) SCase;
      try (simpl; simpl in IHe1; rewrite IHe1; rewrite IHe2; reflexivity).
    SCase "ANum". destruct n;
      simpl; rewrite IHe2; reflexivity.  Qed.

Fixpoint optimize_0plus_bexp (e:bexp) : bexp :=
  match e with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a b => BEq (optimize_0plus a) (optimize_0plus b)
  | BLe a b => BLe (optimize_0plus a) (optimize_0plus b)
  | BNot a => BNot (optimize_0plus_bexp a)
  | BAnd a b => BAnd (optimize_0plus_bexp a) (optimize_0plus_bexp b)
  end.

Tactic Notation "bexp_cases" tactic(first) ident(c) :=
  first;
  [Case_aux c "BTrue" | Case_aux c "BFalse"
  | Case_aux c "BEq" | Case_aux c "BLe" 
  | Case_aux c "BNot" | Case_aux c "BAnd"].

Theorem optimize_0plus_bexp_sound : forall e,
  beval(e) = beval(optimize_0plus_bexp e).
Proof.
  intros.
  bexp_cases (induction e) Case;
    try(simpl);
    try(remember (aeval a =? aeval a0));
    try(destruct b;
    [apply beq_nat_eq in Heqb | symmetry in Heqb ; apply beq_nat_false in Heqb];
    rewrite optimize_0plus_sound with (e:=a0);
    rewrite optimize_0plus_sound with (e:=a));
    try(reflexivity).
    
    rewrite Heqb.
    apply beq_nat_refl.
    symmetry.
    apply not_eq_beq_false.
    apply Heqb.
    
    rewrite IHe.
    reflexivity.
    
    rewrite IHe1.
    rewrite IHe2.
    reflexivity.
Qed.

Fixpoint optimize_0plus (a:aexp) : aexp :=
  






