CoInductive stream (A : Type) := cons {
  hd : A;
  tl : stream A;
}.

CoInductive bisim {A} (s1 s2 : stream A) := bisim_cons {
  hd_eq : s1.(hd _) = s2.(hd _);
  tl_eq : bisim s1.(tl _) s2.(tl _);
}.

Lemma bisim_corect : forall A L,
  (forall (s1 s2 : stream A), L s1 s2 ->
    prod
      (s1.(hd _) = s2.(hd _))
      (L s1.(tl _) s2.(tl _))) ->
  (forall (s1 s2 : stream A), L s1 s2 -> bisim s1 s2).
Proof.
intros A L IH.
cofix bisim_corect; intros s1 s2 l.
constructor.
+ apply (IH s1 s2 l).
+ apply bisim_corect, IH, l.
Qed.
