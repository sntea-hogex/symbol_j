Require Export poly_j.

Theorem plus_n_n_injective_take2 : forall n m,
  n + n = m + m ->
  n = m.
Proof.
  intros.
  generalize dependent n.
  induction m as [| m'].
  Case "m = 0".
    intros.
    destruct n as [| n'].
    SCase "n = 0".
      reflexivity.
    SCase "n = S n'".
      simpl in H.
      inversion H.
  Case "m = S m'".
    intros.
    simpl in H.
    destruct n as [| n'].
    SCase "n = 0". inversion H.
    SCase "n = S n'".
      simpl in H.
      rewrite plus_comm in H.
      rewrite plus_comm with (n := m') in H.
      simpl in H.
      inversion H.
      apply IHm' in H1.
      rewrite H1.
      reflexivity.
Qed.

Theorem index_after_last : forall (n : nat) (X : Type) (l : list X),
  length l = n ->
  index (S n) l = None.
Proof.
  intros.
  generalize dependent n.
  induction l as [| x l'].
  Case "l = []".
    intros.
    simpl in H.
    rewrite <- H.
    reflexivity.
  Case "l = x::l'".
    simpl.
    intros.
    simpl in H.
    destruct n as [| n'].
    SCase "n = 0".
      inversion H.
    SCase "n = S n'".
      inversion H.
      apply IHl'.
      reflexivity.
Qed.







