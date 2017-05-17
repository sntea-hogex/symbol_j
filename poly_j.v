(* Add LoadPath "./". *)

Require Export list_j.

Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

Check (cons nat 2 (cons nat 1 (nil nat))).

Fixpoint length (X:Type) (l:list X) : nat :=
  match l with
  | nil _ => O
  | cons _ h t => S (length X t)
  end.

Fixpoint app (X : Type) (l1 l2 : list X) : (list X) :=
  match l1 with
  | nil _ => l2
  | cons _ h t => cons X h (app X t l2)
  end.

Fixpoint snoc (X:Type) (l:list X) (v:X) : (list X) :=
  match l with
  | nil _ => cons X v (nil X)
  | cons _ h t => cons X h (snoc X t v)
  end.

Fixpoint rev (X:Type) (l:list X) : list X :=
  match l with
  | nil _ => nil X
  | cons _ h t => snoc X (rev X t) h
  end.

Fixpoint app' X l1 l2 : list X :=
  match l1 with
  | nil _ => l2
  | cons _ h t => cons X h (app' X t l2)
  end.

Implicit Arguments nil [[X]].
Implicit Arguments cons [[X]].
Implicit Arguments length [[X]].
Implicit Arguments app [[X]].
Implicit Arguments rev [[X]].
Implicit Arguments snoc [[X]].

Definition mynil : list nat := nil.

Check @nil.

Definition mylil' := @nil nat.

Notation "x :: y" := (cons x y) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y []) .. ).
Notation "x ++ y" := (app x y) (at level 60, right associativity).

Fixpoint repeat (X : Type) (n : X) (count : nat) : list X :=
  match count with
  | O => nil
  | S count' => n :: repeat X n count'
  end.

Example test_repeat1:
  repeat bool true 2 = cons true (cons true nil).
  Proof. reflexivity. Qed.

Theorem nil_app : forall X:Type, forall l:list X,
  app [] l = l.
Proof.
  intros.
  reflexivity.
Qed.

Theorem rev_snoc : forall X:Type,
                   forall v : X,
                   forall s : list X,
  rev (snoc s v) = v :: (rev s).
Proof.
  intros.
  induction s.
    reflexivity.
    simpl. rewrite IHs. reflexivity.
Qed.

Theorem snoc_with_append : forall X : Type,
                  forall l1 l2 : list X,
                  forall v : X,
  snoc(l1 ++ l2) v = l1 ++ (snoc l2 v).
Proof.
  intros.
  induction l1.
    reflexivity.
    simpl. rewrite IHl1. reflexivity.
Qed.

Inductive prod (X Y : Type) : Type :=
  pair : X -> Y -> prod X Y.
Implicit Arguments pair [[X] [Y]].

Notation "( x , y )" := (pair x y).

Notation "X * Y":= (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X*Y) : X :=
  match p with (x,y) => x end.

Definition snd {X Y : Type} (p : X*Y) : Y :=
  match p with (x,y) => y end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y) : list (X*Y) :=
  match (lx,ly) with
  | ([],_) => []
  | (_,[]) => []
  | (x::tx, y::ty) => (x,y) ::(combine tx ty)
  end.

Check @combine.

Eval simpl in (combine [1,2] [false,false,true,true]).

Fixpoint split {X Y : Type} (l : list (X*Y)) : (list X)*(list Y) := 
  match l with
  | nil => (nil,nil)
  | (x,y)::t => match split t with
                      (l1,l2) => (x::l1,y::l2)
                end
  end.

Example test_split:
  split [(1,false),(2,false)] = ([1,2],[false,false]).
Proof. reflexivity.  Qed.

Inductive option (X:Type) : Type :=
  | Some : X -> option X
  | None : option X.
Implicit Arguments Some [[X]].
Implicit Arguments None [[X]].

Fixpoint index {X : Type} (n : nat)
                (l : list X) : option X :=
  match l with
  | [] => None
  | a::l' => if beq_nat n 0 then Some a else index (pred n) l'
  end.

Definition hd_opt {X : Type} (l : list X) : option X :=
  match l with
  | [] => None
  | h::t => Some h
  end.

Check @hd_opt.

Example test_hd_opt1 :  hd_opt [1,2] = Some 1.
 Proof. reflexivity. Qed.
Example test_hd_opt2 :   hd_opt  [[1],[2]]  = Some [1].
 Proof. reflexivity. Qed.

Definition doit3times {X:Type} (f:X->X) (n:X) : X :=
  f (f (f n)).

Check @doit3times.

Example test_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity.  Qed.

Example test_doit3times': doit3times negb true = false.
Proof. reflexivity.  Qed.

Definition plus3 := plus 3.
Check plus3.

Example test_plus3 :    plus3 4 = 7.
Proof. reflexivity.  Qed.
Example test_plus3' :   doit3times plus3 0 = 9.
Proof. reflexivity.  Qed.
Example test_plus3'' :  doit3times (plus 3) 0 = 9.
Proof. reflexivity.  Qed.

Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z := f (fst p) (snd p).

Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry : forall (X Y Z : Type) (f : X -> Y -> Z) x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  intros.
  reflexivity.
Qed.

Theorem curry_uncurry : forall (X Y Z : Type) (f : (X*Y) -> Z) (p : X*Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  intros.
  unfold prod_uncurry.
  unfold prod_curry.
  destruct p.
  reflexivity.
Qed.

Fixpoint filter {X:Type} (test: X->bool) (l:list X)
                : (list X) :=
  match l with
  | []     => []
  | h :: t => if test h then h :: (filter test t)
                        else       filter test t
  end.

Definition length_is_1 {X : Type} (l : list X) : bool := beq_nat (length l) 1.

Definition filter_even_gt7 (l : list nat) : list nat := filter (fun n => andb (evenb n) (ble_nat 7 n)) l.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1,2,6,9,10,3,12,8] = [10,12,8].
Proof. reflexivity. Qed.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5,2,6,19,129] = [].
Proof. reflexivity. Qed.

Definition partition {X : Type} (test : X -> bool) (l : list X) : list X * list X := (filter test l, filter (fun x => negb (test x)) l).

Example test_partition1: partition oddb [1,2,3,4,5] = ([1,3,5], [2,4]).
Proof. reflexivity. Qed.
Example test_partition2: partition (fun x => false) [5,9,0] = ([], [5,9,0]).
Proof. reflexivity. Qed.

Fixpoint map {X Y:Type} (f:X-> Y) (l:list X)
              : (list Y) :=
  match l with
  | [] => []
  | h::t => (f h) :: (map f t)
  end.

Lemma map_snoc : forall (X Y : Type) (f : X -> Y) (l : list X) (x : X),
  map f (snoc l x) = snoc (map f l) (f x).
Proof.
  intros.
  induction l.
  Case "l = []".
    reflexivity.
  Case "l = x0::l".
    simpl. rewrite IHl. reflexivity.
Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros.
  induction l.
  Case "l = nil".
    reflexivity.
  Case "l = x::l".
    simpl.
    rewrite map_snoc.
    rewrite <- IHl.
    reflexivity.
Qed.


Fixpoint flat_map {X Y : Type} (f:X-> list Y) (l:list X) : list Y :=
  match l with
  | [] => []
  | h::t => f h ++ flat_map f t
  end.


Example test_flat_map1:
  flat_map (fun n => [n,n,n]) [1,5,4]
  = [1, 1, 1, 5, 5, 5, 4, 4, 4].
Proof. reflexivity. Qed.

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
                      : option Y :=
  match xo with
    | None => None
    | Some x => Some (f x)
  end.

Fixpoint fold {X Y:Type} (f: X->Y->Y) (l:list X) (b:Y) : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

Definition constfun {X: Type} (x: X) : nat->X :=
  fun (k:nat) => x.

Definition override {X: Type} (f: nat -> X) (k:nat) (x:X) : nat->X :=
  fun (k':nat) => if beq_nat k k' then x else f k'.

Theorem override_example : forall (b:bool),
  (override (constfun b) 3 true) 2 = b.
Proof.
  destruct b.
  reflexivity.
  reflexivity.
Qed.

Theorem unfold_example_bad : forall m n,
  3 + n = m -> plus3 n+1 = m+1.
Proof.
  intros m n H.
  unfold plus3.
  rewrite H.
  reflexivity. Qed.

Theorem override_eq : forall {X:Type} x k (f:nat->X),
  (override f k x) k = x.
Proof.
  intros X x k f.
  unfold override.
  rewrite <- beq_nat_refl.
  reflexivity. Qed.

Theorem override_neq : forall {X:Type} x1 x2 k1 k2 (f : nat->X),
  f k1 = x1 -> beq_nat k2 k1 = false -> (override f k2 x2) k1 = x1.
Proof.
  intros.
  unfold override.
  rewrite H0.
  rewrite H.
  reflexivity.
Qed.

Theorem eq_add_S : forall (n m : nat),
  S n = S m -> n = m.
Proof.
  intros n m eq. inversion eq. reflexivity. Qed.

Theorem silly4 : forall (n m : nat),
  [n] = [m] -> n = m.
Proof.
  intros n o eq. inversion eq. reflexivity. Qed.

Theorem silly5 : forall(n m o : nat),
  [n,m] = [o,o] -> [n] = [m].
Proof.
  intros n m o eq. inversion eq. reflexivity. Qed.

Example sillyex1 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j -> y :: l = x :: j -> x = y.
Proof.
  intros.
  inversion H.
  inversion H0.
  rewrite H2.
  reflexivity.
Qed.

Theorem silly6 : forall(n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra.
  inversion contra.
Qed.

Theorem silly7 : forall (n m : nat),
  false = true -> [n] = [m].
Proof.
  intros n m contra. inversion contra. Qed.

Example sillyex2 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = [] ->
  y :: l = z :: j ->
  x = z.
Proof.
  intros. inversion H. Qed.

Lemma eq_remove_S : forall n m,
  n = m -> S n = S m.
Proof.
  intros n m eq. rewrite -> eq. reflexivity. Qed.

Theorem beq_nat_eq : forall n m,
  true = beq_nat n m -> n = m.
Proof.
  intros n. induction n as [| n'].
  Case "n ~ 0".
    intros m. destruct m as [| m'].
    SCase "m = 0". reflexivity.
    SCase "m = S m'". simpl. intros contra. inversion contra.
  Case "n = S n".
    intros m. destruct m as [| m'].
    SCase "m = 0". simpl. intros contra. inversion contra.
    SCase "m = S m". simpl. intros H.
      apply eq_remove_S. apply IHn'. apply H. Qed.

Theorem beq_nat_eq' : forall m n,
  beq_nat n m = true -> n = m.
Proof.
  intros m. induction m as [| m'].
  Case "m ~ O".
    intros n.
    SearchAbout beq_nat.
    rewrite <- beq_nat_sym.
    destruct n.
      reflexivity.
      intros. inversion H.
  Case "m = S m'".
    intros n.
    induction n as[| n'].
    SCase "n = O".
      rewrite beq_nat_sym.
      intros.
      inversion H.
    SCase "n = S n'".
      simpl.
      intros.
      assert (n' = m' -> S n' = S m').
        intros.
        rewrite H0.
        reflexivity.
      apply H0.
      apply IHm'.
      apply H.
Qed.

Theorem length_snoc' : forall (X : Type) (v : X) (l : list X) (n : nat),
  length l = n ->
  length (snoc l v) = S n.
Proof.
  intros X v l. induction l as [| v' l'].
  Case "l = []". intros n eq. rewrite <- eq. reflexivity.
  Case "l = v' :: l'". intros n eq. simpl. destruct n as [| n'].
    SCase "n = 0". inversion eq.
    SCase "n = S n".
      apply eq_remove_S. apply IHl'. inversion eq. reflexivity. Qed.

Theorem beq_nat_0_l : forall n,
  true = beq_nat 0 n -> 0 = n.
Proof.
  intros.
  apply beq_nat_eq.
  apply H.
Qed.

Theorem beq_nat_0_r : forall n,
  true = beq_nat n 0 -> 0 = n.
Proof.
  intros.
  symmetry.
  apply beq_nat_eq.
  apply H.
Qed.

Theorem double_injective : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
  (* WORKED IN CLASS *)
    Case "n = 0". simpl. intros m eq. destruct m as [| m'].
      SCase "m = 0". reflexivity.
      SCase "m = S m'". inversion eq.
    Case "n = S n'". intros m eq. destruct m as [| m'].
      SCase "m = 0". inversion eq.
      SCase "m = S m'".
        apply eq_remove_S. apply IHn'. inversion eq. reflexivity. Qed.

Theorem S_inj : forall (n m : nat) (b : bool),
     beq_nat (S n) (S m) = b  ->
     beq_nat n m = b.
Proof.
  intros n m b H. simpl in H. apply H.  Qed.

Theorem silly3' : forall (n : nat),
  (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
     true = beq_nat n 5  ->
     true = beq_nat (S (S n)) 7.
Proof.
  intros n eq H.
  symmetry in H. apply eq in H. symmetry in H.
  apply H.  Qed.

Theorem plus_n_n_indective : forall n m,
  n+n = m+m -> n = m.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    intros. simpl in H.
    destruct m as [| m'].
    SCase "m = O". reflexivity.
    SCase "m = S m'". inversion H.
  Case "n = S n".
    intros. simpl in H.
    destruct m as [| m'].
    SCase "m = O". simpl in H. inversion H.
    SCase "m = S m'".
      simpl in H. inversion H.
      assert(m' + S m' = S m' + m').
        SSCase "Proof of assertion".
        apply plus_comm.
      rewrite plus_comm in H1.
      rewrite H0 in H1.
      simpl in H1.
      inversion H1.
      apply IHn' in H3.
      rewrite H3.
      reflexivity.
Qed.

Definition sillyfun (n : nat) : bool :=
  if beq_nat n 3 then false
  else if beq_nat n 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (beq_nat n 3).
    Case "beq_nat n 3 = true". reflexivity.
    Case "beq_nat n 3 = false". destruct (beq_nat n 5).
    SCase "beq_nat n 5 = true". reflexivity.
    SCase "beq_nat n 5 = false". reflexivity. Qed.

Theorem override_shadow : forall {X:Type} x1 x2 k1 k2 (f : nat->X),
  (override (override f k1 x2) k1 x1) k2 = (override f k1 x1) k2.
Proof.
  intros.
  unfold override.
  destruct (beq_nat k1 k2).
  Case "beq_nat k1 k2 = true". reflexivity.
  Case "beq_nat k1 k2  = false". reflexivity.
Qed.


Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l. induction l as [| [x y] l'].
  Case "l = []".
    simpl.
    intros.
    inversion H.
    reflexivity.
  Case "l = cons (x y) l'".
    simpl. destruct (split l') as [l1' l2'].
    intros.
    inversion H.
    simpl.
    assert(combine l1' l2' = l' -> (x, y) :: combine l1' l2' = (x, y) :: l').
    SCase "Proof of assertion".
      intros.
      rewrite H0.
      reflexivity.
    apply H0.
    apply IHl'.
    reflexivity.
Qed.

Theorem split_combine : forall X Y (l1 : list X) (l2 : list Y),
  length l1 = length l2 -> split (combine l1 l2) = (l1, l2).
Proof.
  intros X Y l1.
  induction l1 as [| x l1'].
  Case "l1 = []".
    intros.
    assert (l2 = []).
    SCase "Proof of assertion".
      simpl in H.
      destruct l2.
      SSCase "l2 = []".
        reflexivity.
      SSCase "l2 = y::l2".
        inversion H.
    rewrite H0.
    reflexivity.
  Case "l1 = x::l1'".
    simpl.
    intros.
    destruct l2 as [| y l2'].
    SCase "l2 = []".
      inversion H.
    SCase "l2 = y :: l2".
      simpl.
      assert(length l1' = length l2' -> split (combine l1' l2') = (l1', l2')).
        apply IHl1'.
      destruct (split (combine l1' l2')) as [ls1 ls2].
      assert ((ls1,ls2) = (l1', l2') -> (x::ls1, y::ls2) = (x::l1', y::l2')) as Ha.
      SSCase "Proof of assertion".
        intros.
        inversion H1.
        reflexivity.
    apply  Ha.
    apply H0.
    simpl in H.
    inversion H.
    reflexivity.
Qed.

Definition sillyfun1 (n : nat) : bool :=
  if beq_nat n 3 then true
  else if beq_nat n 5 then true
  else false.

Theorem silly_fun1_odd : forall (n : nat),
  sillyfun1 n = true ->
  oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  remember (beq_nat n 3) as e3.
  destruct (e3).
    Case "e3 = true ". apply beq_nat_eq in Heqe3.
      rewrite -> Heqe3. reflexivity.
    Case "e3 = false".
      remember (beq_nat n 5) as e5. destruct e5.
        SCase "e5 = true".
          apply beq_nat_eq in Heqe5.
          rewrite Heqe5. reflexivity.
        SCase "e5 = false". inversion eq. Qed.

Theorem override_same : forall {X : Type} x1 k1 k2 (f : nat->X),
  f k1 = x1 ->
  (override f k1 x1) k2 = f k2.
Proof.
  intros.
  unfold override.
  remember (beq_nat k1 k2) as b.
  destruct (b).
  Case "b = true".
    apply beq_nat_eq in Heqb.
    rewrite Heqb in H.
    symmetry.
    apply H.
  Case "b = false". reflexivity.
Qed.

Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                             (x : X) (l lf : list X),
     filter test l = x :: lf ->
     test x = true.
Proof.
  intros X test x l.
  induction l.
  Case "l = []".
    intros.
    simpl in H.
    inversion H.
  Case "l = x0 :: l".
    intros.
    simpl in H.
    remember (test x0).
    destruct b.
    inversion H.
    rewrite <- H1.
    symmetry.
    apply Heqb.
    assert (filter test l = x::lf -> test x = true).
      apply IHl.
    apply H0.
    apply H.
Qed.

Example trans_eq_example : forall (a b c d e f : nat),
     [a,b] = [c,d] ->
     [c,d] = [e,f] ->
     [a,b] = [e,f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. rewrite -> eq2. reflexivity.  Qed.

Theorem trans_eq : forall {X:Type} (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity.  Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
     [a,b] = [c,d] ->
     [c,d] = [e,f] ->
     [a,b] = [e,f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m:=[c,d]). apply eq1. apply eq2.   Qed.

Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  intros.
  apply trans_eq with (m0:=m).
  apply H0.
  apply H.
Qed.

Theorem beq_nat_trans : forall n m p,
  true = beq_nat n m ->
  true = beq_nat m p ->
  true = beq_nat n p.
Proof.
  intros.
  apply beq_nat_eq in H.
  apply beq_nat_eq in H0.
  assert (n = p).
  apply trans_eq with (m0:=m).
  apply H.
  apply H0.
  rewrite H.
  rewrite H0.
  apply beq_nat_refl.
Qed.

Theorem override_permute : forall {X:Type} x1 x2 k1 k2 k3 (f : nat->X),
  false = beq_nat k2 k1 ->
  (override (override f k2 x2) k1 x1) k3 = (override (override f k1 x1) k2 x2) k3.
Proof.
  intros.
  unfold override.
  remember (beq_nat k1 k3).
  remember (beq_nat k2 k3).
  destruct b.
  Case "b = true".
    destruct b0.
    SCase "b0 = true".
      apply beq_nat_eq in Heqb.
      apply beq_nat_eq in Heqb0.
      assert(k1 = k2).
        apply trans_eq with (m:=k3).
        apply Heqb.
        symmetry.
        apply Heqb0.
      rewrite H0 in H.
      rewrite <- beq_nat_refl in H.
      inversion H.
    SCase "b0 = false".
      reflexivity.
  Case "b = false".
    destruct b0.
    SCase "b0 = true".
      reflexivity.
    SCase "b0 = false".
      reflexivity.
Qed.




