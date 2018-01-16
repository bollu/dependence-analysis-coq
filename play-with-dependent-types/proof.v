Definition useGt0 (n: nat) (witness: n > 0) : nat :=
  10.


Definition createGt0(n: nat) : nat :=
  match n with
  | O => 42
  | S(n') => useGt0 n  (#???)
  end.
