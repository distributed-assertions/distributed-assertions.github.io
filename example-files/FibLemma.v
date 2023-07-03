Require Import Arith Lia.

Fixpoint fib (n: nat): nat :=
  match n with
  | 0 => 0
  | S j =>
      match j with
      | 0 => 1
      | S k => fib j + fib k
      end
  end.

Ltac liarw F :=
  let h := fresh "H" in
  assert (h: F) by (simpl; lia); rewrite h in *; clear h.

Lemma fib_square_lemma: forall n, 2 * n + 27 <= fib (n + 12).
Proof.
  induction n.
  - simpl; lia.
  - liarw (n + 12 = S (n + 11)).
    liarw (S n + 12 = S (S (n + 11))).
    assert (Hl: 2 <= fib (n + 11)).
      clear IHn; induction n; [simpl; lia | ].
      liarw (n + 11 = S (n + 10)).
      liarw (S n + 11 = S (S (n + 10))).
      assert (H: fib (S (S (n + 10)))
                 = fib (S (n + 10)) + fib (n + 10)) by auto.
      lia.
    assert (fib (S (S (n + 11)))
            = fib (S (n + 11)) + fib (n + 11)) by auto.
    lia.
Qed.

Theorem fib_square_above: forall n, 13 <= n -> n ^ 2 < fib n.
Proof.
  intros n Hle; pose (k := n - 13); liarw (n = k + 13); clear Hle.
  induction k.
  - simpl; lia.
  - liarw (k + 13 = S (k + 12)).
    liarw (S k + 13 = S (S (k + 12))).
    assert (fib (S (S (k + 12)))
            = fib (S (k + 12)) + fib (k + 12)) by auto.
    liarw (S (S (k + 12)) ^ 2
           = S (k + 12) ^ 2 + 2 * k + 27).
    specialize (fib_square_lemma k).
    lia.
Qed.
