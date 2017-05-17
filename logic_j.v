Require Export prop_j.

Definition funny_prop1 := forall n, forall (E : ev n), ev (n+4).

Definition funny_prop1' := forall n, forall (_ : ev n), ev (n+4).

Definition funny_prop1'' := forall n, ev n -> ev(n+4).

Inductive and (P Q : Prop) : Prop :=
  conj : P -> Q -> (and P Q).

Notation "P /\ Q" := (and P Q) : type_scope.

Check conj.

Theorem and_example :
  (ev 0) /\ (ev 4).
Proof.
  apply conj.
  apply ev_0.
  apply ev_SS. apply ev_SS. apply ev_0. Qed.

Print and_example.

Theorem proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q H.
  inversion H as [HP HQ].
  apply HP. Qed.

Theorem proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros.
  inversion H as [HP HQ]. 
  apply HQ. Qed.

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q H.
  inversion H as [HP HQ].
  split.
    apply HQ.
    apply HP.
Qed.

Print and_commut.

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R H.
  inversion H as [HP [HQ HR]].
  apply conj.
  apply conj.
  apply HP.
  apply HQ.
  apply HR.
Qed.

Theorem even_ev : forall n : nat,
  (even n -> ev n) /\ (even (S n) -> ev (S n)).
Proof.
  intros.
  induction n as [| n'].
  Case "n = 0".
    apply conj.
    SCase "left".
      intros. apply ev_0.
    SCase "right".
      intros. inversion H.
  Case "n = S n'".
    inversion IHn'.
    apply conj.
    SCase "left".
      intros. apply H0. apply H1.
    SCase "right".
      unfold even. simpl. intros. apply ev_SS. 
      apply H. unfold even. apply H1.
Qed.

Definition conj_fact : forall P Q R,
  P /\ Q -> Q /\ R -> P /\ R :=
  fun (P Q R : Prop) (H : P /\ Q) (H0 : Q /\ R) =>
    match H with
    | conj _ _ HP HQ =>
      match H0 with
      | conj _ _ HQ HR => conj P R HP HR
      end
    end.

Definition iff(P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q) 
                      (at level 95, no associativity) : type_scope.

Theorem iff_implies : forall P Q : Prop,
  (P <-> Q) -> P -> Q.
Proof.
  intros P Q H.
  inversion H as [HAB HBA]. apply HAB.  Qed.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q H.
  inversion H as [HAB HBA].
  split.
    Case "->". apply HBA.
    Case "<-". apply HAB.  Qed.

Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof.
  intros. split.
    intros. apply H.
    intros. apply H.
Qed.


Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros. inversion H. inversion H0.
  split.
    Case "->". intros. apply H3. apply H1. apply H5.
    Case "<-". intros. apply H2. apply H4. apply H5.
Qed.

SearchAbout MyProp.
Print iff.

Definition MyProp_iff_ev : forall n, MyProp n <-> ev n :=
  fun (n:nat) => conj (MyProp n -> ev n) (ev n -> MyProp n) (ev_MyProp n) (MyProp_ev n).

Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q.

Notation "P \/ Q" := (or P Q) : type_scope.

Check or_introl.
Check or_intror.

Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros P Q H.
  inversion H as [HP | HQ].
    Case "right". apply or_intror. apply HP.
    Case "left". apply or_introl. apply HQ.  Qed.

Theorem or_commut' : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros P Q H.
  inversion H as [HP | HQ].
    Case "right". right. apply HP.
    Case "left". left. apply HQ.  Qed.

Definition or_commut_object : forall P Q : Prop, P \/ Q -> Q \/ P := 
  fun (P Q : Prop) (H : P \/ Q) =>
    match H with
    | or_introl _ _ HP => or_intror _ _ HP
    | or_intror _ _ HQ => or_introl _ _ HQ
    end.

Theorem or_distributes_over_and_1 : forall P Q R : Prop,
  P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R. intros H. inversion H as [HP | [HQ HR]].
    Case "left". split.
      SCase "left". left. apply HP.
      SCase "right". left. apply HP.
    Case "right". split.
      SCase "left". right. apply HQ.
      SCase "right". right. apply HR.  Qed.

Theorem or_distributes_over_and_2 : forall P Q R : Prop,
  (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
  intros.
  inversion H.
  inversion H0 as [HP | HQ].
    SCase "left". left. apply HP.
    SCase "right".
      inversion H1 as [HP | HR].
        Case "left". left. apply HP.
        Case "right".
          right. apply conj. apply HQ. apply HR.
Qed.

Theorem or_distrubutes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros. unfold iff. apply conj.
    Case "->".
    intros. inversion H.
      SCase "left".
      apply conj. left. apply H0. left. apply H0.
      SCase "right".
      inversion H0.
      apply conj. right. apply H1. right. apply H2.
    Case "<-".
      apply or_distributes_over_and_2.
Qed.

Theorem andb_true__and : forall b c,
  andb b c = true -> b = true /\ c = true.
Proof.
  (* WORKED IN CLASS *)
  intros b c H.
  destruct b.
    Case "b = true". destruct c.
      SCase "c = true". apply conj. reflexivity. reflexivity.
      SCase "c = false". inversion H.
    Case "b = false". inversion H.  Qed.

Theorem and__andb_true : forall b c,
  b = true /\ c = true -> andb b c = true.
Proof.
  (* WORKED IN CLASS *)
  intros b c H.
  inversion H.
  rewrite H0. rewrite H1. reflexivity. Qed.

Theorem andb_false : forall b c,
  andb b c = false -> b = false \/ c = false.
Proof.
  intros. unfold andb in H. destruct b.
    Case "b = true". right. apply H.
    Case "b = false". left. apply H.
Qed.

Theorem orb_true : forall b c,
  orb b c = true -> b = true \/ c = true.
Proof.
  intros. unfold orb in H. destruct b.
    Case "b = true". left. reflexivity.
    Case "b = false". right. apply H.
Qed.

Theorem orb_false : forall b c,
  orb b c = false -> b = false /\ c = false.
Proof.
  intros. unfold orb in H. destruct b.
    Case "b = true". inversion H.
    Case "b = false". apply conj. reflexivity. apply H.
Qed.

Inductive False : Prop := .

Theorem False_implies_nonsense :
  False -> 2 + 2 = 5.
Proof.
  intros contra.
  inversion contra.  Qed.

Theorem nonsense_implies_False :
  2 + 2 = 5 -> False.
Proof.
  intros contra.
  inversion contra.  Qed.

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros P contra.
  inversion contra.  Qed.

Inductive True : Prop := 
  | true_constructer : True.

Print True_ind.

Definition not (P:Prop) := P -> False.
Notation "~ x" := (not x) : type_scope.

Check not.

Theorem not_False :
  ~ False.
Proof.
  unfold not. intros H. inversion H.  Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  (* WORKED IN CLASS *)
  intros P Q H. inversion H as [HP HNA]. unfold not in HNA.
  apply HNA in HP. inversion HP.  Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  (* WORKED IN CLASS *)
  intros P H. unfold not. intros G. apply G. apply H.  Qed.

Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
  unfold not. intros. apply H0. apply H. apply H1.
Qed.

Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  unfold not. intros. inversion H. apply H1. apply H0.
Qed.

Theorem five_not_even :
  ~ ev 5.
Proof.
  unfold not. intros.
  inversion H. inversion H1. inversion H3.
Qed.

Theorem ev_not_ev_S : forall n,
  ev n -> ~ ev (S n).
Proof.
  intros. unfold not. induction H.
    Case "ev_0". intros. inversion H.
    Case "ev_SS".
      intros.
      apply IHev.
      apply ev_minus2 in H0.
      simpl in H0.
      apply H0.
Qed.

Definition peirce := forall P Q: Prop,
  ((P->Q)->P)->P.
Definition classic := forall P:Prop,
  ~~P -> P.
Definition excluded_middle := forall P:Prop,
  P \/ ~P.
Definition de_morgan_not_and_not := forall P Q:Prop,
  ~(~P/\~Q) -> P\/Q.
Definition implies_to_or := forall P Q:Prop,
  (P->Q) -> (~P\/Q).

Theorem peirce__classic :
  peirce -> classic.
Proof.
  unfold peirce. unfold classic. unfold not.
  intros. apply H with (Q:=False). intros.
  apply H0 in H1. inversion H1.
Qed.

Theorem classic__excluded_middle :
  classic -> excluded_middle.
Proof.
  unfold classic. unfold excluded_middle. unfold not.
  intros H Q.  apply H. intros.
  apply H0. right. intros. apply H0. left. apply H1.
Qed.

Theorem excluded_middle__de_morgan_not_and_not : 
  excluded_middle -> de_morgan_not_and_not.
Proof.
  unfold excluded_middle.
  unfold de_morgan_not_and_not.
  unfold not.
  intros. assert (P \/ ~P).
    Case "Proof of Assertion". apply H.
  unfold not in H1. inversion H1.
    Case "left". left. apply H2.
    Case "right".
      assert (Q \/ ~Q).
        SCase "Proof of Assertion". apply H.
      unfold not in H3.
      inversion H3.
        SCase "left". right. apply H4.
        SCase "right".
          assert (False).
            SSCase "Proof of assertion".
              apply H0.
              apply conj. apply H2. apply H4.
          inversion H5.
Qed.

Theorem de_morgan_not_and_not__implies_to_or :
  de_morgan_not_and_not -> implies_to_or.
Proof.
  unfold de_morgan_not_and_not.
  unfold implies_to_or.
  unfold not.
  intros. apply H. intros. inversion H1.
  apply H2. intros. apply H3.
  apply H0. apply H4.
Qed.

Theorem implies_to_or__excluded_middle :
  implies_to_or -> excluded_middle.
Proof.
  unfold implies_to_or.
  unfold excluded_middle.
  intros.
  apply or_commut.
  apply H.
  intros. apply H0.
Qed.

Theorem implies_to_or__peirce :
  implies_to_or -> peirce.
Proof.
  unfold peirce.
  unfold not.
  intros H.
  intros P Q.
  assert excluded_middle.
    apply implies_to_or__excluded_middle.
    apply H.
  unfold excluded_middle in H0.
  intros.
  assert (Q \/ ~Q).
    apply H0.
  inversion H2.
  apply H1.
  intros.
  apply H3.
  assert (P \/ ~P).
    apply H0.
  inversion H4.
  apply H5.
  apply H1.
  intros.
  unfold not in H5.
  apply H5 in H6.
  inversion H6.
Qed.

Notation "x <> y" := (~ (x = y)) : type_scope.

Theorem not_false_then_true : forall b : bool,
  b <> false -> b = true.
Proof.
  intros b H. destruct b.
  Case "b = true". reflexivity.
  Case "b = false".
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.   Qed.

Theorem not_eq_beq_false : forall n n' : nat,
  n <> n' ->
  beq_nat n n' = false.
Proof.
  intros n.
  unfold not.
  induction n.
    Case "n = 0".
    intros.
    destruct n'.
      assert (0 = 0). reflexivity.
      apply H in H0. inversion H0.
      simpl. reflexivity.
    intros.
    Case "n = S n".
    destruct n'.
      simpl. reflexivity.
      simpl. apply IHn. intros.
      apply H. rewrite H0. reflexivity.
Qed.

Theorem beq_false_not_eq : forall n m,
  false = beq_nat n m -> n <> m.
Proof.
  unfold not.
  intros n.
  induction n as [| n'].
  Case "n = 0".
    intros.
    destruct m.
      inversion H.
      intros. inversion H0.
  Case "n = S n'".
    intros.
    destruct m.
      inversion H0.
      inversion H0. generalize H2.
      apply IHn'. simpl in H. apply H.
Qed.

Inductive ex (X:Type) (P : X -> Prop) : Prop :=
  ex_intro : forall (witness:X), P witness -> ex X P.

Definition some_nat_is_even : Prop :=
  ex nat ev.

Definition snie : some_nat_is_even :=
  ex_intro _ ev 4 (ev_SS 2 (ev_SS 0 ev_0)).

Notation "'exists' x , p" := (ex _ (fun x => p))
  (at level 200, x ident, right associativity) : type_scope.
Notation "'exists' x : X , p" := (ex _ (fun x:X => p))
  (at level 200, x ident, right associativity) : type_scope.

Example exists_example_1 : exists n, n + (n * n) = 6.
Proof.
  apply ex_intro with (witness:=2).
  reflexivity.  Qed.

Example exists_example_1' : exists n,
     n + (n * n) = 6.
Proof.
  exists 2.
  reflexivity.  Qed.

Theorem exists_example_2 : forall n,
     (exists m, n = 4 + m) ->
     (exists o, n = 2 + o).
Proof.
  intros n H.
  inversion H as [m Hm].
  exists (2 + m).
  apply Hm.  Qed.

Definition p : ex nat (fun n => ev (S n)) :=
  ex_intro nat (fun n => ev (S n)) 1 (ev_SS 0 ev_0).

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros.
  unfold not.
  intros.
  inversion H0 as [x IHE].
  apply IHE. apply H.
Qed.

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  unfold excluded_middle.
  intros excluded_middle.
  unfold not.
  intros X P Hnen x.
  assert (P x \/ ~(P x)).
    Case "Proof of Assertion". apply excluded_middle.
  inversion H.
  apply H0.
  assert (exists x : X , ~(P x)).
    Case "Proof of Assertion". exists x. apply H0.
  apply Hnen in H1. inversion H1.
Qed.

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros.
  unfold iff.
  apply conj.
  Case " -> ".
    intros.
    inversion H.
    inversion H0.
      SCase "left".
        left. exists witness. apply H1.
      SCase "right".
        right. exists witness. apply H1.
  Case "<-".
    intros.
    inversion H.
      SCase "left". inversion H0.
        exists witness. left. apply H1.
      SCase "right". inversion H0.
        exists witness. right. apply H1.
Qed.

Module MyEquality.

Inductive eq (X:Type) : X -> X -> Prop :=
  refl_equal : forall x, eq X x x.

Notation "x = y" := (eq _ x y)
                    (at level 70, no associativity) : type_scope.

Inductive eq' (X:Type) (x:X) : X -> Prop :=
    refl_equal' : eq' X x x.

Notation "x =' y" := (eq' _ x y)
                     (at level 70, no associativity) : type_scope.

Theorem two_defs_of_eq_coincide : forall (X:Type) (x y : X),
  x = y <-> x =' y.
Proof.
  unfold iff.
  intros. apply conj.
      Case "->". intros. inversion H. apply refl_equal'.
      Case "<-". intros. inversion H. apply refl_equal.
Qed.

Check eq'_ind.

Definition four : 2 + 2 = 1 + 3 :=
  refl_equal nat 4.
Definition singleton : forall (X:Set) (x:X), []++[x] = x::[]  :=
  fun (X:Set) (x:X) => refl_equal (list X) [x].

End MyEquality.

Module LeFirstTry.

Inductive le : nat -> nat -> Prop :=
  | le_n : forall n, le n n
  | le_S : forall n m, (le n m) -> (le n (S m)).

End LeFirstTry.

Inductive le (n:nat) : nat -> Prop :=
  | le_n : le n n
  | le_S : forall m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).

Check le_ind.

Theorem test_le1 :
  3 <= 3.
Proof.
  (* WORKED IN CLASS *)
  apply le_n.  Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  (* WORKED IN CLASS *)
  apply le_S. apply le_S. apply le_S. apply le_n.  Qed.

Theorem test_le3 :
  ~ (2 <= 1).
Proof.
  (* WORKED IN CLASS *)
  intros H. inversion H. inversion H1.  Qed.

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

Inductive square_of : nat -> nat -> Prop :=
  sq : forall n:nat, square_of n (n * n).

Inductive next_nat (n:nat) : nat -> Prop :=
  | nn : next_nat n (S n).

Inductive next_even (n:nat) : nat -> Prop :=
  | ne_1 : ev (S n) -> next_even n (S n)
  | ne_2 : ev (S (S n)) -> next_even n (S (S n)).

Inductive total_relation (n m:nat) : Prop :=
  | con_total_relation : total_relation n m.

Inductive empty_relation (n m : nat) : Prop :=
  .

Module R.

Inductive R : nat -> nat -> nat -> Prop :=
   | c1 : R 0 0 0
   | c2 : forall m n o, R m n o -> R (S m) n (S o)
   | c3 : forall m n o, R m n o -> R m (S n) (S o)
   | c4 : forall m n o, R (S m) (S n) (S (S o)) -> R m n o
   | c5 : forall m n o, R m n o -> R n m o.

Theorem hoge : R 1 1 2.
Proof.
  apply c2. apply c3. apply c1. Qed.

Lemma R_plus : forall (m n o : nat),
  R m n o -> m + n = o.
Proof.
  intros.
  induction H.
  reflexivity. simpl. rewrite IHR. reflexivity.
  rewrite plus_comm. simpl. rewrite plus_comm. rewrite IHR. reflexivity.
  simpl in IHR. rewrite plus_comm in IHR. simpl in IHR. inversion IHR. apply plus_comm.
  rewrite plus_comm. apply IHR.
Qed.

Theorem hogee : ~ R 2 2 6.
Proof.
  unfold not. intros. apply R_plus in H. inversion H.
Qed.

Lemma R_plus' : forall(n m : nat),
  R n m (n+m).
Proof.
  intros.
  induction n as [| n'].
    Case "n = 0".
      induction m as [| m'].
        SCase "m = 0". apply c1.
        SCase "m = S m'". apply c3. apply IHm'.
    Case "n = S n'".
      induction m as [| m'].
        SCase "m = 0". rewrite plus_0_r.
          apply c2. simpl in IHn'.
          rewrite plus_0_r in IHn'.
          apply IHn'.
        SCase "m = S m'". simpl. apply c2. apply IHn'.
Qed.

Theorem R_fact : forall (m n o : nat),
  R m n o <-> m+n = o.
Proof.
  intros. unfold iff. split.
  Case "->". apply R_plus.
  Case "<-". intros. rewrite <- H. apply R_plus'.
Qed.

End R.

(*all_forallb*)

Inductive all (X : Type) (P : X -> Prop) : list X -> Prop :=
  | conallnil : all X P []
  | conall : forall(h : X) (t : list X),
             P h -> all X P t -> all X P (h::t)
.

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
    | [] => true
    | x :: l' => andb (test x) (forallb test l')
  end.

Theorem forallb_prop :
  forall (X : Type) (test : X -> bool) (l : list X),
    forallb test l = true
    <-> all X (fun(x:X) => test x = true) l.
Proof.
  intros. split.
  Case "->".
    intros.
    induction l as [| h t].
      SCase "l = []". apply conallnil.
      SCase "l = h::t".
        simpl in H.
        apply conall.
        apply andb_true_elim1 in H.
        apply H.
        apply andb_true_elim2 in H.
        apply IHt.
        apply H.
  Case "<-".
    intros.
    induction H.
      SCase "nil". reflexivity.
      SCase "h::t".
        simpl. rewrite H. rewrite IHall. reflexivity.
Qed.

(*filter_challenge*)
(*filter_challenge2*)
(*no_repeats*)
Inductive appears_in {X:Type} (a:X) : list X -> Prop :=
  | ai_here : forall l, appears_in a (a::l)
  | ai_later : forall b l, appears_in a l -> appears_in a (b::l).

Lemma appears_in_app : forall {X:Type} (xs ys : list X) (x:X),
     appears_in x (xs ++ ys) -> appears_in x xs \/ appears_in x ys.
Proof.
  intros.
  remember (xs++ys).
  generalize dependent xs.
  generalize dependent ys.
  induction H.
  Case "ai_here".
    intros.
    destruct xs.
    SCase "[]".
      simpl in Heql.
      rewrite <- Heql.
      right.
      apply ai_here.
    SCase "x::xs".
      simpl in Heql.
      inversion Heql.
      left.
      apply ai_here.
  Case "ai_later".
    intros.
    destruct xs.
    SCase "[]".
      right.
      simpl in Heql.
      rewrite <- Heql.
      apply ai_later.
      apply H.
    SCase "x0::xs".
      inversion Heql.
      apply IHappears_in in H2.
      inversion H2.
      left.
      apply ai_later.
      apply H0.
      right.
      apply H0.
Qed.

Lemma app_appears_in_right : forall {X : Type} (xs ys : list X) (x:X),
  appears_in x ys -> appears_in x (xs++ys).
Proof.
  intros.
  inversion H.
  induction xs.
    apply ai_here.
    simpl. apply ai_later. apply IHxs.
  induction xs.
    simpl. apply ai_later. apply H0.
    simpl. apply ai_later. apply IHxs.
Qed.

Lemma app_appears_in : forall {X:Type} (xs ys : list X) (x:X),
     appears_in x xs \/ appears_in x ys -> appears_in x (xs ++ ys).
Proof.
  intros.
  inversion H.
  Case "left".
    induction H0.
    SCase "[]".
      simpl.
      apply ai_here.
      simpl.
      apply ai_later.
      apply IHappears_in.
      left.
      apply H0.
  Case "right".
    apply app_appears_in_right.
    apply H0.
Qed.

Definition disjoint {X:Type} (l1 l2 : list X) : Prop :=
  forall (x:X), appears_in x l1 -> appears_in x l2 -> False.

Inductive no_repeats {X:Type} : list X -> Prop :=
  | no_repeats_nil : no_repeats []
  | no_repeats_con : forall a l, no_repeats l ->
    (appears_in a l -> False) -> no_repeats (a::l).

Theorem app_no_repeats : forall {X:Type} (xs ys : list X),
  no_repeats (xs++ys) -> no_repeats xs /\ no_repeats ys.
Proof.
  intros.
  split.
  Case "right".
    remember (xs++ys).
    generalize dependent xs.
    generalize dependent ys.
    induction H.
    SCase "no_repeats_nil".
      intros.
      destruct xs.
        apply no_repeats_nil.
        inversion Heql.
    SCase "no_repeats_con".
      intros.
      destruct xs.
      SSCase "no_repeats_nil".
        apply no_repeats_nil.
      SSCase "no_repeats_con".
        apply no_repeats_con.
        inversion Heql.
        apply IHno_repeats with (ys:=ys).
        apply H3.
        inversion Heql.
        intros.
        apply H0.
        rewrite H3.
        apply app_appears_in.
        left.
        rewrite H2.
        apply H1.
  Case "left".
    remember (xs++ys).
    generalize dependent xs.
    generalize dependent ys.
    induction H.
    SCase "no_repeats_nil".
      intros.
      destruct xs.
      SSCase "nil".
        simpl in Heql.
        rewrite <- Heql.
        apply no_repeats_nil.
      SSCase "x::xs".
        inversion Heql.
    SCase "no_repeats_con".
      intros.
      destruct xs.
        SSCase "nil".
          simpl in Heql.
          rewrite <- Heql.
          apply no_repeats_con.
            apply H.
            apply H0.
        SSCase "x::xs".
        apply IHno_repeats with (xs:=(xs)).
        inversion Heql.
          reflexivity.
Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros.
  induction n.
    apply le_n.
    apply le_S.
    apply IHn.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros.
  induction m as [| m'].
    Case "0".
      inversion H.
      apply le_n.
    Case "S m'".
      inversion H.
        apply le_n.
        apply le_S.
        apply IHm'.
      apply H1.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros n m.  generalize dependent n.  induction m.
  Case "m = 0".
    intros.
    inversion H.
      SCase "le_n".
        apply le_n.
      SCase "le_S".
        inversion H1.
  Case "m = S m".
    intros.
    inversion H.
      apply le_n.
      apply le_S.
      apply IHm.
      apply H1.
Qed.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intros.
  induction b.
  Case "0". rewrite plus_0_r. apply le_n.
  Case "S b".
    rewrite plus_comm. simpl. apply le_S.
   rewrite plus_comm. apply IHb.
Qed.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
  unfold "<".
  intros.
  split.
  Case "left".
    induction H.
    apply n_le_m__Sn_le_Sm.
    apply le_plus_l.
    apply le_S.
    apply IHle.
  Case "right".
    induction H.
    apply n_le_m__Sn_le_Sm.
    rewrite plus_comm.
    apply le_plus_l.
    apply le_S.
    apply IHle.
Qed.

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  unfold "<".
  intros.
  apply le_S.
  apply H.
Qed.

Theorem ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.
Proof.
  intros n m H.
  generalize dependent m.
  induction n.
  Case "0".
    intros.
    assert(m = 0+m). reflexivity.
    rewrite H0.
    apply le_plus_l.
  Case "S n".
    intros.
    destruct m.
    SCase "0". inversion H. simpl in H.
    SCase "S m".
      apply n_le_m__Sn_le_Sm.
      apply IHn.
      apply H.
Qed.

Theorem ble_nat_n_Sn_false : forall n m,
  ble_nat n (S m) = false ->
  ble_nat n m = false.
Proof.
  intros.
  generalize dependent m.
  induction n as [| n'].
    Case "0". intros. simpl in H. inversion H.
    Case "S n".
      intros.
      destruct m as [| m'].
      SCase "0". reflexivity.
      SCase "S m". simpl. apply IHn'. apply H.
Qed.

Theorem ble_nat_refl : forall n:nat,
  true = ble_nat n n.
Proof.
  intros.
  induction n as [| n'].
    reflexivity.
    simpl.
    apply IHn'.
Qed.

Theorem ble_nat_false : forall n m,
  ble_nat n m = false -> ~(n <= m).
Proof.
  unfold "~".
  intros.
  induction H0.
    Case "le_n".
      rewrite <- ble_nat_refl in H.
      inversion H.
    Case "le_S".
      apply IHle.
      apply ble_nat_n_Sn_false.
      apply H.
Qed.

Inductive nostutter : list nat -> Prop :=
  | nostutter_nil : nostutter []
  | nostutter_one : forall n:nat, nostutter [n]
  | nostutter_mul : forall (n h : nat) (t:list nat),
                      nostutter (h::t) -> n<>h ->
                      nostutter (n::h::t).

Example test_nosutter_1 : nostutter [3,1,4,1,5,6].
Proof. repeat constructor; apply beq_false_not_eq; auto. Qed.

Example test_nostutter_2:  nostutter [].
Proof. repeat constructor; apply beq_false_not_eq; auto. Qed.

Example test_nostutter_3:  nostutter [5].
Proof. repeat constructor; apply beq_false_not_eq; auto. Qed.

Example test_nostutter_4: not (nostutter [3,1,1,4]).
Proof. intro.
repeat match goal with
  h: nostutter _ |- _ => inversion h; clear h; subst
end.
contradiction H5; auto. Qed.

Lemma app_length : forall {X:Type} (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros.
  Print "++".
  induction l1.
  Case "nil".
    reflexivity.
  Case "x::l1".
    simpl. SearchAbout (S _ = S _).
    apply eq_S.
    apply IHl1.
Qed.

Lemma appears_in_app_split : forall {X:Type} (x:X) (l:list X),
  appears_in x l ->
  exists l1, exists l2, l = l1 ++ (x::l2).
Proof.
  intros.
  induction H.
  Case "ai_here".
    apply ex_intro with (witness := nil).
    apply ex_intro with (witness := l).
    reflexivity.
  Case "ai_later".
    inversion IHappears_in.
    inversion H0.
    rewrite H1.
    apply ex_intro with (witness:=b::witness).
    apply ex_intro with (witness:=witness0).
    reflexivity.
Qed.

Inductive repeats {X:Type} : list X -> Prop :=
  | repeats_here : forall (a:X) (l:list X), 
                   appears_in a l -> repeats (a::l)
  | repeats_later : forall (b:X) (l:list X),
                    repeats l -> repeats (b::l).

Theorem Sn_lt_Sn__n_lt_m : forall (n m : nat),
  S n < S m -> n < m.
Proof.
  unfold "<".
  intros. apply Sn_le_Sm__n_le_m. apply H.
Qed.





Lemma lt_irrefl : forall n, ~ n < n.
Proof.
 induction n.
  intro. inversion H.

  intro. destruct IHn.
  apply Sn_le_Sm__n_le_m. apply H.
Qed.

Lemma lt_not_le: forall n m : nat, n < m -> ~ m <= n.
Proof.
 intros.
 induction H.
  apply lt_irrefl.

  intro. destruct IHle. inversion H0.
   apply le_S. apply le_n.

   rewrite <- H2 in H0. apply le_S. apply Sn_le_Sm__n_le_m. apply H0.
Qed. 

Lemma bag_remove : forall {X:Type} (l1 l2 l3 : list X) (x:X),
  ~(appears_in x l1) ->
  (forall (v:X), appears_in v (x::l1) -> appears_in v (l2++(x::l3))) ->
  (forall (v:X), appears_in v l1 -> appears_in v (l2++l3)).
Proof.
  intros.
  assert (appears_in v (l2++x::l3) -> appears_in v (l2++l3)).
    Case "Proof of Assertion".
    intros. apply app_appears_in. apply appears_in_app in H2.
    inversion H2.
      SCase "left". left. apply H3.
      SCase "right". right. inversion H3.
        rewrite H5 in H1. apply H in H1. inversion H1.
        apply H5.
  apply H2. apply H0. apply ai_later. apply H1.
Qed.

Theorem pigeonhole_principle: forall {X:Type} (l1 l2:list X),
  excluded_middle ->
  (forall x, appears_in x l1 -> appears_in x l2) ->
  length l2 < length l1 ->
  repeats l1.
Proof.
  unfold excluded_middle.
  intros X l1. induction l1.
  SCase "[]".
    intros.
    inversion H1.
  SCase "x::l1".
    intros.
    assert(appears_in x l2). apply H0. apply ai_here.
    assert (appears_in x l1 \/ ~(appears_in x l1)).
      apply H with (P:=(appears_in x l1)).
    inversion H3.
    SSCase "appears_in x l1".
      apply repeats_here.
      apply H4.
    SSCase "~appears_in x l1".
      apply repeats_later.
      apply appears_in_app_split in H2.
      inversion H2.
      inversion H5.
      apply IHl1 with (l2:=witness++witness0).
      apply H.
      apply bag_remove with (x0:=x).
        apply H4. rewrite <- H6. apply H0.
      assert (S(length(witness++witness0)) = length(witness++x::witness0)).
        SSSCase "Proof of Assertion".
        rewrite app_length.
        rewrite app_length with (l4:=x::witness0).
        simpl. rewrite plus_n_Sm. reflexivity.
    apply Sn_lt_Sn__n_lt_m.
    rewrite H7.
    rewrite <- H6.
    apply H1.
Qed.

Print nat_ind. Print nat_rect.

Definition nat_ind2 :
    forall (P : nat -> Prop),
    P 0 ->
    P 1 ->
    (forall n : nat, P n -> P (S(S n))) ->
    forall n : nat , P n :=
       fun P => fun P0 => fun P1 => fun PSS =>
          fix f (n:nat) := match n return P n with
                             0 => P0
                           | 1 => P1
                           | S (S n') => PSS n' (f n')
                          end.

Print nat_ind.

Lemma even_ev' : forall n, even n -> ev n.
Proof.
 intros.
 induction n as [ | |n'] using nat_ind2.
  Case "even 0".
    apply ev_0.
  Case "even 1".
    inversion H.
  Case "even (S(S n'))".
    apply ev_SS.
    apply IHn'.  unfold even.  unfold even in H.  simpl in H. apply H.
Qed.











