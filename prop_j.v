(* Add LoadPath "/". *)

Require Export poly_j.

Definition plus_fact : Prop := 2+2 = 4.
Check plus_fact.

Theorem plus_fact_is_true :
  plus_fact.
Proof. reflexivity. Qed.

Definition strange_prop1 : Prop :=
  (2+2 = 5) -> (99+26 = 42).

Definition strange_prop2 :=
  forall n, (ble_nat n 17 = true) -> (ble_nat n 99 = true).

Definition even (n:nat) : Prop :=
  evenb n = true.

Check even.
Check(even 4).
Check(even 3).

Definition even_n__even__SSn (n:nat) : Prop :=
  (even n) -> (even (S (S n))).

Definition between (n m o: nat) : Prop :=
  andb (ble_nat n o) (ble_nat o m) = true.

Definition teen : nat -> Prop := between 13 19.

Definition true_for_zero (P:nat->Prop) : Prop :=
  P 0.

Definition true_for_n__true_for_Sn (P:nat->Prop) (n:nat) : Prop :=
  P n -> P (S n).

Definition preserved_by_S (P:nat->Prop) : Prop :=
  forall n', P n' -> P (S n').

Definition true_for_all_numbers (P:nat->Prop) : Prop :=
  forall n, P n.

Definition our_nat_induction (P:nat->Prop) : Prop :=
  (true_for_zero P) ->
  (preserved_by_S P) ->
  (true_for_all_numbers P).

Inductive good_day : day ->  Prop :=
  | gd_sat : good_day saturday
  | gd_sun : good_day sunday.

Theorem gds : good_day sunday.
Proof. apply gd_sun. Qed.

Inductive day_before : day -> day -> Prop :=
  | db_tue : day_before tuesday monday
  | db_wed : day_before wednesday tuesday
  | db_thu : day_before thursday wednesday
  | db_fri : day_before friday thursday
  | db_sat : day_before saturday friday
  | db_sun : day_before sunday saturday
  | db_mon : day_before monday sunday.

Inductive fine_day_for_singing : day -> Prop :=
  | fdfs_any : forall d:day, fine_day_for_singing d.

Theorem fdfs_wed : fine_day_for_singing wednesday.
Proof. apply fdfs_any. Qed.

Definition fdfs_wed' : fine_day_for_singing wednesday :=
  fdfs_any wednesday.

Check fdfs_wed.
Check fdfs_wed'.

Inductive ok_day : day -> Prop :=
  | okd_gd : forall d,
      good_day d ->
      ok_day d
  | okd_before : forall d1 d2,
      ok_day d2 ->
      day_before d2 d1 ->
      ok_day d1.

Definition okdw : ok_day wednesday :=
  okd_before wednesday thursday
    (okd_before thursday friday
       (okd_before friday saturday
         (okd_gd saturday gd_sat)
         db_sat)
       db_fri)
    db_thu.

Theorem okdw' : ok_day wednesday.
Proof.
  apply okd_before with (d2:=thursday).
    apply okd_before with (d2:=friday).
      apply okd_before with (d2:=saturday).
        apply okd_gd. apply gd_sat.
        apply db_sat.
      apply db_fri.
   apply db_thu. Qed.

Print okdw'.

Definition okd_before2 := forall d1 d2 d3,
  ok_day d3 ->
  day_before d2 d1 ->
  day_before d3 d2 ->
  ok_day d1.

Theorem okd_before2_valid : okd_before2.
Proof.
  unfold okd_before2.
  intros.
  generalize dependent H0.
  apply okd_before.
  generalize dependent H1.
  apply okd_before.
  apply H.
Qed.

Definition okd_before2_valid' : okd_before2 :=
  fun (d1 d2 d3  : day) =>
  fun (H : ok_day d3) =>
  fun (H0 : day_before d2 d1) =>
  fun (H1 : day_before d3 d2) =>
  okd_before d1 d2 (okd_before d2 d3 H H1) H0.

Print okd_before2_valid.

Check nat_ind.

Theorem mult_0_r' : forall n:nat,
  n*0 = 0.
Proof.
  apply nat_ind.
  Case "O". reflexivity.
  Case "S". simpl. intros n IHn. rewrite -> IHn.
    reflexivity. Qed.

Theorem plus_one_r' : forall n:nat,
  n + 1 = S n.
Proof.
  apply nat_ind.
  Case "O". reflexivity.
  Case "S". intros. simpl. rewrite H. reflexivity.
Qed.

Inductive yesno : Type :=
  | yes : yesno
  | no : yesno.

Check yesno_ind.

Inductive rgb : Type :=
  | red : rgb
  | green :rgb
  | blue : rgb.

Check rgb_ind.

Inductive natlist : Type :=
  | nnil : natlist
  | ncons : nat -> natlist -> natlist.

Check natlist_ind.

Inductive natlist1 : Type :=
  | nnil1 : natlist1
  | nsnoc1 : natlist1 -> nat -> natlist1.

Check natlist1_ind.

Inductive ExSet : Type :=
  | con1 : bool -> ExSet
  | con2 : nat -> ExSet -> ExSet.

Check ExSet_ind.

Inductive tree (X:Type) : Type :=
  | leaf : X -> tree X
  | node : tree X -> tree X -> tree X.
Check tree_ind.

Inductive mytype (X : Type) :=
  | constr1 : X -> mytype X
  | constr2 : nat -> mytype X
  | constr3 : mytype X -> nat -> mytype X.

Check mytype_ind.

Inductive foo (X Y : Type) :=
  | bar : X -> foo X Y
  | baz : Y -> foo X Y
  | quux : (nat -> foo X Y) -> foo X Y.

Check foo_ind.

Definition P_m0r (n:nat) : Prop :=
  n * 0 = 0.

Definition P_m0r' : nat->Prop :=
  fun n =>  n * 0 = 0.

Theorem mult_0_r'' : forall n:nat,
  P_m0r n.
Proof.
  apply nat_ind.
  Case "n = O". reflexivity.
  Case "n = S n'".
    unfold P_m0r. simpl. intros n' IHn'.
    apply IHn'. Qed.

Inductive ev: nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS : forall n:nat, ev n -> ev (S (S n)).

Theorem four_ev' :
  ev 4.
Proof.
  apply ev_SS. apply ev_SS. apply ev_0. Qed.

Definition four_ev : ev 4 :=
  ev_SS 2 (ev_SS 0 ev_0).

Definition ev_plus4 : forall n, ev n -> ev (4+n) :=
  fun(n : nat) => fun(p : ev n)
  => ev_SS (S (S n)) (ev_SS n p).
Theorem ev_plus4' : forall n,
  ev n -> ev (4+n).
Proof.
  intros.
  apply ev_SS.
  apply ev_SS.
  apply H.
Qed.

Theorem double_even : forall n,
  ev (double n).
Proof.
  intros.
  induction n as [| n'].
  Case "n = 0".
    simpl. apply ev_0.
  Case "n = S n'".
    simpl. apply ev_SS. apply IHn'.
Qed.

Theorem ev_minus2: forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  destruct E as [| n' E'].
  Case "E = ev_0". simpl. apply ev_0.
  Case "E = ev_SS n' E'". simpl. apply E'. Qed.

Theorem ev_even : forall n,
  ev n -> even n.
Proof.
  intros n E. induction E as [| n' E'].
  Case "E = ev_0".
    unfold even. reflexivity.
  Case "E = ev_SS n' E'".
    unfold even. apply IHE'. Qed.

Theorem ev_sum : forall n m,
  ev n -> ev m -> ev (n+m).
Proof.
  intros. induction H.
  simpl. apply H0. simpl. apply ev_SS. apply IHev. Qed.

Theorem SSev_ev : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E. inversion E as [| n' E']. apply E'.
Qed.

Theorem SSSSev_even : forall n,
  ev(S (S (S (S  n)))) -> ev n.
Proof.
  intros. inversion H. inversion H1. apply H3.
Qed.

Theorem even5_nonsense:
  ev 5 -> 2+2 = 9.
Proof.
  intros. inversion H. inversion H1. inversion H3.
Qed.

Theorem ev_minu2' : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E. inversion E as [| n' E'].
  Case "E = ev_0". simpl. apply ev_0.
  Case "E = ev_SS n' E'". simpl. apply E'.
Qed.

Theorem ev_ev_even : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  intros.
  induction H0. simpl in H. apply H. inversion H. apply IHev.
  apply H2.
Qed.

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros.
  apply ev_ev_even with (m:=m+p) (n:=n+m).
  replace (n+m+(m+p)) with (n+p+double m).
  apply ev_sum.
  apply H0.
  apply double_even.
  rewrite double_plus.
  rewrite plus_swap.
  rewrite plus_swap with (n:=n+m).
  SearchAbout (_+_+_).
  rewrite <- plus_assoc.
  rewrite <- plus_assoc.
  replace (p+m) with (m+p).
  reflexivity.
  apply plus_comm.
  apply H.
Qed.

Inductive MyProp : nat -> Prop :=
  | MyProp1 : MyProp 4
  | MyProp2 : forall n:nat, MyProp n -> MyProp(4+n)
  | MyProp3 : forall n:nat, MyProp (2+n) -> MyProp n.

Theorem MyProp_ten : MyProp 10.
Proof.
  apply MyProp3. simpl.
  assert (12 = 4 + 8) as H12.
    Case "Proof of assertion". reflexivity.
  rewrite -> H12.
  apply MyProp2.
  assert (8 = 4 + 4) as H8.
    Case "Proof of assertion". reflexivity.
  rewrite -> H8.
  apply MyProp2.
  apply MyProp1.   Qed.

Theorem MyProp_0 : MyProp 0.
Proof.
  apply MyProp3.
  apply MyProp3.
  simpl.
  apply MyProp1.
Qed.

Theorem MyProp_plustwo : forall n:nat, MyProp n -> MyProp (S (S n)).
Proof.
  intros.
  apply MyProp3.
  apply MyProp2.
  apply H.
Qed.

Theorem MyProp_ev : forall n:nat,
  ev n -> MyProp n.
Proof.
  intros n E.
  induction E as [| n' E'].
  Case "E = ev_0".
    apply MyProp_0.
  Case "E = ev_SS n' E'".
    apply MyProp_plustwo. apply IHE'.  Qed.

Theorem ev_MyProp : forall n:nat,
  MyProp n -> ev n.
Proof.
  intros.
  induction H.
  Case "MyProp1". 
    apply ev_SS.
    apply ev_SS.
    apply ev_0.
  Case "MyProp2".
    apply ev_SS.
    apply ev_SS.
    apply IHMyProp.
  Case "MyProp3".
    apply ev_minus2 in IHMyProp.
    simpl in IHMyProp.
    apply IHMyProp.
Qed.

Fixpoint true_upto_n__true_everywhere (n:nat) (f:nat->Prop) : Prop :=
  match n with
  | O => forall m : nat, f m
  | S n' => f n -> (true_upto_n__true_everywhere n' f)
  end.

Example true_upto_n_example :
    (true_upto_n__true_everywhere 3 (fun n => even n))
  = (even 3 -> even 2 -> even 1 -> forall m : nat, even m).
Proof. reflexivity.  Qed.

Check ev_ind.

Theorem ev_even' : forall n,
  ev n -> even n.
Proof.
  apply ev_ind.
  Case "ev_0". unfold even. reflexivity.
  Case "ev_SS". intros n' E' IHE'. unfold even. apply IHE'. Qed.

Check list_ind.
Check ev_ind.
Print MyProp.
Check MyProp_ind.

Theorem ev_MyProp' : forall n:nat,
  MyProp n -> ev n.
Proof.
  apply MyProp_ind.
  Case "MyProp1".
    apply ev_SS. apply ev_SS. apply ev_0.
  Case "MyProp2".
    intros. apply ev_SS. apply ev_SS. apply H0.
  Case "MyProp3".
    intros. apply ev_minus2 in H0. simpl in H0. apply H0.
Qed.


Module P.

(*hgoegeg*)

Inductive p : (tree nat) -> nat -> Prop :=
   | c1 : forall n, p (leaf _ n) 1
   | c2 : forall t1 t2 n1 n2,
            p t1 n1 -> p t2 n2 -> p (node _ t1 t2) (n1 + n2)
   | c3 : forall t n, p t n -> p t (S n).

End P.

