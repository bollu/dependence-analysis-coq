Import EqNotations.
Inductive dep (n: nat) :=
  mkDep : dep n.


Theorem equalTypes (n n': nat): n = n' -> dep n = dep n'.
Proof.
  intros.
  destruct H.
  reflexivity.
Qed.


Theorem equalInhabitants (n n' : nat): forall (H: n = n'),
    (rew H in (mkDep n)) = mkDep n'.
  intros.
  subst. reflexivity.
Qed.
