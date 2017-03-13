(*Add LoadPath "./".*)

Require Export basics_j.

Module NatList.

Inductive natprod : Type :=
  pair : nat -> nat -> natprod.

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Notation "( x , y )" := (pair x y).

Eval simpl in (fst (3,4)).

Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.

Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd(n,m)).
Proof.
  reflexivity. Qed.

Theorem surjective_pairing_stuck : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p. destruct p as (n,m). reflexivity.
Qed.

Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  destruct p as (n,m).
  reflexivity.
Qed.

Inductive natlist : Type :=
  |nil : natlist
  |cons : nat -> natlist -> natlist.

Definition l_123 := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

Fixpoint repeat (n count : nat) : natlist := 
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l : natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Fixpoint app(l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y) (right associativity, at level 60).

Definition hd (default : nat) (l : natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tail (l:natlist) : natlist := 
  match l with
  | nil => nil
  | h :: t => t
  end.

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  | nil => nil
  | O::t => nonzeros t
  | h::t => h::(nonzeros t)
  end.

Example test_nonzeros:            nonzeros [0,1,0,2,3,0,0] = [1,2,3].
  Proof. reflexivity. Qed.

Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h::t => match (evenb h) with
            | false => h::(oddmembers t)
            | true => oddmembers t
          end
  end.

Example test_oddmembers:            oddmembers [0,1,0,2,3,0,0] = [1,3].
  Proof. reflexivity. Qed.

Fixpoint countoddmembers (l:natlist) : nat :=
  match l with
  | nil => O
  | h::t => match (evenb h) with
            | false => S (countoddmembers t)
            | true => countoddmembers t
          end
  end.

Example test_countoddmembers1:    countoddmembers [1,0,3,1,4,5] = 4.
 Proof. reflexivity. Qed.
Example test_countoddmembers2:    countoddmembers [0,2,4] = 0.
 Proof. reflexivity. Qed.
Example test_countoddmembers3:    countoddmembers nil = 0.
  Proof. reflexivity. Qed.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h1::t1 => match l2 with
            | nil => l1
            | h2::t2 => h1::h2::(alternate t1 t2)
            end
  end.

Example test_alternate1:        alternate [1,2,3] [4,5,6] = [1,4,2,5,3,6].
 Proof. reflexivity. Qed.
Example test_alternate2:        alternate [1] [4,5,6] = [1,4,5,6].
 Proof. reflexivity. Qed.
Example test_alternate3:        alternate [1,2,3] [4] = [1,4,2,3].
 Proof. reflexivity. Qed.
Example test_alternate4:        alternate [] [20,30] = [20,30].
 Proof. reflexivity. Qed.

Definition bag := natlist.

Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
  | nil => O
  | h::t => match (beq_nat h v) with
            | true => S (count v t)
            | false => (count v t)
            end
  end.

Example test_count1:              count 1 [1,2,3,1,4,1] = 3.
 Proof. reflexivity. Qed.
Example test_count2:              count 6 [1,2,3,1,4,1] = 0.
 Proof. reflexivity. Qed.

Definition sum : bag -> bag -> bag :=
  app.

Example test_sum1:              count 1 (sum [1,2,3] [1,4,1]) = 3.
 Proof. reflexivity. Qed.

Definition add (v:nat) (s:bag) : bag :=
  cons v s.

Example test_add1:                count 1 (add 1 [1,4,1]) = 3.
 Proof. reflexivity. Qed.
Example test_add2:                count 5 (add 1 [1,4,1]) = 0.
 Proof. reflexivity. Qed.

Definition member (v:nat) (s:bag) : bool :=
  negb (beq_nat O (count v s)).

Example test_member1:             member 1 [1,4,1] = true.
 Proof. reflexivity. Qed.
Example test_member2:             member 2 [1,4,1] = false.
 Proof. reflexivity. Qed.

Theorem nil_app : forall l : natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

Theorem tl_length_pred : forall l : natlist,
  pred (length l) = length(tail l).
Proof.
  intros l. destruct l as [| n l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons n l'".
    reflexivity. Qed.

Theorem app_ass : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros. induction l1 as [| n l1'].
  Case "l1 = nil".
    reflexivity.
  Case "l1 = cons n l1'".
    simpl. rewrite -> IHl1'. reflexivity. Qed.

Theorem app_length : forall l1 l2 : natlist,
  length(l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros.
  induction l1.
  Case "l1 = nil".
    reflexivity.
  Case "l1 = n::l1".
    simpl.
    rewrite -> IHl1.
    reflexivity.
Qed.

Fixpoint snoc (l:natlist) (v:nat) : natlist :=
  match l with
  | nil => [v]
  | h::t => h::(snoc t v)
  end.

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h::t => snoc (rev t) h
  end.

Theorem length_snoc : forall n : nat, forall l : natlist,
  length (snoc l n) = S (length l).
Proof.
  intros n l. induction l as [| n' l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons n' l'".
    simpl. rewrite -> IHl'. reflexivity. Qed.

Theorem rev_length : forall l : natlist,
  length(rev l) = length l.
Proof.
  intros l. induction l as[| n l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons".
    simpl. rewrite -> length_snoc.
    rewrite IHl'. reflexivity. Qed.

Theorem app_nil_end : forall l : natlist,
  l ++ [] = l.
Proof.
  intros.
  induction l.
  Case "l = nil".
    reflexivity.
  Case "l = n :: l".
    simpl.
    rewrite IHl.
    reflexivity.
  Qed.

Theorem rev_snoc : forall l : natlist, forall n : nat,
  rev (snoc l n) = n::(rev l).
Proof.
  intros.
  induction l.
  Case "l = nil".
    reflexivity.
  Case "l = n0::l".
    simpl.
    rewrite IHl.
    reflexivity.
Qed.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intros.
  induction l.
  Case "l = nil".
    reflexivity.
  Case "l = n::l".
    simpl.
    rewrite rev_snoc.
    rewrite IHl.
    reflexivity.
Qed.


Lemma distr_rev_ : forall l1 l2 : natlist, forall n : nat,
  snoc (l1 ++ l2) n = l1 ++ snoc l2 n.
Proof.
  intros.
  induction l1.
  Case "l1 = nil".
    reflexivity.
  Case "l1 = n0::l1".
    simpl.
    rewrite IHl1.
    reflexivity.
Qed.


Theorem distr_rev : forall l1 l2 : natlist,
  rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof.
  intros.
  induction l1.
  Case "l1 = nil".
    simpl.
    rewrite app_nil_end.
    reflexivity.
  Case "l1 = n::1".
    simpl.
    rewrite IHl1.
    rewrite distr_rev_.
    reflexivity.
Qed.

Theorem app_ass4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros.
  rewrite app_ass.
  rewrite app_ass.
  reflexivity.
Qed.

Theorem snoc_append : forall (l:natlist) (n:nat),
  snoc l n = l ++ [n].
Proof.
  intros.
  induction l.
  reflexivity.
  simpl.
  rewrite IHl.
  reflexivity.
Qed.

Lemma nonzeros_length : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros.
  induction l1.
  Case "l1 = nil".
    reflexivity.
  Case "l1 = n::l1".
    destruct n.
      simpl.
      rewrite IHl1.
      reflexivity.
      simpl.
      rewrite IHl1.
      reflexivity.
Qed.

Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.

Fixpoint index (n:nat) (l:natlist) : natoption :=
  match l with
  | nil => None
  | a :: l' => match beq_nat n 0 with
              | true => Some a
              | false => index (pred n) l'
              end
  end.

Fixpoint index' (n:nat) (l:natlist) : natoption :=
  match l with
  | nil => None
  | a :: l' => if beq_nat n 0 then Some a else index (pred n) l'
  end.

Definition option_elim (o : natoption) (d : nat) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

Definition hd_opt (l : natlist) : natoption :=
  match l with
  | nil => None
  | h::t => Some h
  end.

Example test_hd_opt1 : hd_opt [] = None.
  Proof. reflexivity. Qed.

Example test_hd_opt2 : hd_opt [1] = Some 1.
 Proof. reflexivity. Qed.

Example test_hd_opt3 : hd_opt [5,6] = Some 5.
 Proof. reflexivity. Qed.

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim (hd_opt l) default.
Proof.
  intros.
  destruct l.
  reflexivity.
  reflexivity.
Qed.

Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
  match l1 with
  | nil => match l2 with
          | nil => true
          | h::t => false
          end
  | h1::t1 => match l2 with
            | nil => false
            | h2::t2 => if beq_nat h1 h2
                          then beq_natlist t1 t2 
                          else false
            end
  end.

Theorem beq_natlist_ref1 : forall l:natlist,
  true = beq_natlist l l.
Proof.
  induction l.
  Case "l = nil".
    reflexivity.
  Case "l = n::l".
    simpl.
    assert (true = beq_nat n n).
      induction n.
      reflexivity.
      simpl. rewrite IHn. reflexivity.
   rewrite <- H.
   rewrite IHl.
   reflexivity.
Qed.

Theorem silly1 : forall (n m o p : nat),
  n = m ->
  [n,o] = [n,p] -> 
  [n,o] = [m,p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  apply eq2. Qed.

Theorem silly2 : forall (n m o p : nat),
  n = m ->
  (forall (q r : nat), q = r -> [q,o] = [r,p]) ->
  [n,o] = [m,p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1. Qed.

Theorem silly2a : forall (n m : nat),
     (n,n) = (m,m)  ->
     (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
     [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1.  Qed.

Theorem silly_ex :
  (forall n, evenb n = true -> oddb (S n) = true) ->
  evenb 3 = true ->
  oddb 4 = true.
Proof.
  intros.
  apply H.
  apply H0.
Qed.

Theorem silly3 : forall(n:nat),
  true = beq_nat n 5 ->
  beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  symmetry.
  simpl. apply H. Qed.

Theorem rev_exercise1 : forall (l l' : natlist),
  l = rev l' ->
  l' = rev l.
Proof.
  intros.
  rewrite H.
  symmetry.
  rewrite rev_involutive.
  reflexivity.
Qed.

Theorem beq_nat_sym : forall (n m : nat),
  beq_nat n m = beq_nat m n.
Proof.
  intros n. induction n as [ | n'].
  Case "n = O".
    intros m.
    destruct m.
      reflexivity.
      reflexivity.
  Case "n = S n'".
    intros m.
    destruct m.
      reflexivity.
      simpl. apply IHn'.
Qed.

End NatList.

Module Dictionary.

Inductive dictionary : Type :=
  | empty : dictionary
  | record : nat -> nat -> dictionary -> dictionary.

Definition insert (key value : nat) (d : dictionary) :
dictionary :=
  (record key value d).

Fixpoint find (key : nat) (d : dictionary) : option nat:=
  match d with
  | empty => None
  | record k v d' => if (beq_nat key k) then (Some v) else (find key d')
  end.

Theorem dictionary_invariant1 : forall (d : dictionary) (k v: nat),
  (find k (insert k v d)) = Some v.
Proof.
  intros.
  simpl.
  assert(beq_nat k k = true).
    induction k.
      reflexivity.
      simpl. apply IHk.
  rewrite H. reflexivity.
Qed.

Theorem dictionary_invariant2 : forall (d : dictionary) (m n o: nat),
  (beq_nat m n) = false -> (find m d) = (find m (insert n o d)).
Proof.
  intros.
  simpl.
  rewrite H.
  reflexivity.
Qed.

End Dictionary.

Definition beq_nat_sym := NatList.beq_nat_sym.



