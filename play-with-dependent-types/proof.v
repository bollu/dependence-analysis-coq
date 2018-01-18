

Lemma add_lhs_sub_rhs_stays_equal: forall (n m total: nat), (S n) + m = total -> n + (S m) = total.
Proof.
  intros.
  omega.

Definition fuel_to_nat (fuel: nat) (n: nat) (max: nat) (witness1: fuel + nat = max)
           (witness2: /\ n > 0) :=
  match fuel with
  | O => 42
  | S fuel' => fuel_to_nat fuel' (n + 1) max  
           
                  

