```{.lprolog title="fib.sig"}
sig fib.
kind nat type.
type z nat.
type s nat -> nat.
type plus nat -> nat -> nat -> o.
type times nat -> nat -> nat -> o.
type fib nat -> nat -> o.
```

```{.lprolog title="fib.mod"}
module fib.
plus z X X.
plus (s X) Y (s Z) :- plus X Y Z.
times z X z.
times (s X) Y Z :- times X Y U, plus Y U Z.
fib z z.
fib (s z) (s z).
fib (s (s X)) Y :- fib (s X) U, fib X V, plus U V Y.
```

```{.abella title="FibExample.thm"}
Kind nat type.
Type z nat.
Type s nat -> nat.

Define nat: nat -> prop by
; nat z
; nat (s X) := nat X.

Define lt: nat -> nat -> prop by
; lt z (s X)
; lt (s X) (s Y) := lt X Y.

Define leq: nat -> nat -> prop by
; leq z X
; leq (s X) (s Y) := leq X Y.

Define plus: nat -> nat -> nat -> prop by
; plus z X X
; plus (s X) Y (s Z) := plus X Y Z.

Define times: nat -> nat -> nat -> prop by
; times z X z
; times (s X) Y Z := exists U, times X Y U /\ plus U Y Z.

Define fib: nat -> nat -> prop by
; fib z z
; fib (s z) (s z)
; fib (s (s X)) K :=
    exists M N, fib X M /\ fib (s X) N /\ plus M N K.

Import "damf:bafyreid5eco3yl6uewtahf4zhyzl5rgai7qzbyfmpy6gk6hknbclgradye" as
Theorem fib_square_above: forall x, nat x ->
  leq (s^13 z) x ->
  forall y, times x x y ->
  forall u, fib x u -> lt y u.
%% skip.

Theorem plus_deterministic: forall x y u v, plus x y u -> plus x y v -> u = v.
induction on 1. intros. case H1.
  case H2. search.
  case H2. apply IH to *H3 *H4. search.

Theorem times_deterministic: forall x y u v, times x y u -> times x y v -> u = v.
induction on 1. intros. case H1.
  case H2. search.
  case H2. apply IH to *H3 *H5. apply plus_deterministic to *H4 *H6. search.

Theorem fib_deterministic: forall x y u, fib x y -> fib x u -> y = u.
induction on 1. intros. case H1.
  case H2. search.
  case H2. search.
  case H2.
    apply IH to *H3 *H6.
    apply IH to *H4 *H7.
    apply plus_deterministic to *H5 *H8. search.

Theorem lt_irreflexive: forall x, nat x -> lt x x -> false.
induction on 1. intros. case H1.
  case H2.
  case H2. apply IH to *H3 *H4.

Theorem plus_result_nat: forall x y k, nat x -> nat y -> plus x y k -> nat k.
induction on 3. intros. case H3.
  search.
  case H1. apply IH to *H5 *H2 *H4. search.

Theorem times_result_nat: forall x y k, nat x -> nat y -> times x y k -> nat k.
induction on 3. intros. case H3.
  search.
  case H1. apply IH to *H6 H2 *H4. apply plus_result_nat to *H7 *H2 *H5. search.

Theorem fib_squares: forall x x2, nat x -> times x x x2 ->
  (fib x x2 -> x = z \/ x = s z \/ x = s^12 z) /\
  (x = z \/ x = s z \/ x = s^12 z -> fib x x2).
intros Hnat Hsquare. split.
%% ->
intros Hfib.
Hcs: assert x = s^0 z \/ x = s^1 z \/ x = s^2 z \/ x = s^3 z
         \/ x = s^4 z \/ x = s^5 z \/ x = s^6 z \/ x = s^7 z
         \/ x = s^8 z \/ x = s^9 z \/ x = s^10 z \/ x = s^11 z
         \/ x = s^12 z \/ leq (s^13 z) x.
  Hnat: case Hnat. search.
  Hnat: case Hnat. search.
  Hnat: case Hnat. search.
  Hnat: case Hnat. search.
  Hnat: case Hnat. search.
  Hnat: case Hnat. search.
  Hnat: case Hnat. search.
  Hnat: case Hnat. search.
  Hnat: case Hnat. search.
  Hnat: case Hnat. search.
  Hnat: case Hnat. search.
  Hnat: case Hnat. search.
  Hnat: case Hnat. search.
  right. search 14.
Hcs: case Hcs.
  search. % case of x = z
  search. % case of x = s z
  % case of x = 2
  Ha: assert fib (s^2 z) (s z).
  apply fib_deterministic to Ha Hfib.
  Hsquare_ground: assert times (s^2 z) (s^2 z) (s^4 z).
  apply times_deterministic to Hsquare Hsquare_ground.
  % case of x = 3
  Ha: assert fib (s^3 z) (s^2 z).
  apply fib_deterministic to Ha Hfib.
  Hsquare_ground: assert 9 times (s^3 z) (s^3 z) (s^9 z).
  apply times_deterministic to Hsquare Hsquare_ground.
  % case of x = 4
  Ha: assert fib (s^4 z) (s^3 z).
  apply fib_deterministic to Ha Hfib.
  Hsquare_ground: assert 16 times (s^4 z) (s^4 z) (s^16 z).
  apply times_deterministic to Hsquare Hsquare_ground.
  % case of x = 5
  Ha: assert fib (s^5 z) (s^5 z).
  apply fib_deterministic to Ha Hfib.
  Hsquare_ground: assert 25 times (s^5 z) (s^5 z) (s^25 z).
  apply times_deterministic to Hsquare Hsquare_ground.
  % case of x = 6
  Ha: assert 10 fib (s^6 z) (s^8 z).
  apply fib_deterministic to Ha Hfib.
  Hsquare_ground: assert 36 times (s^6 z) (s^6 z) (s^36 z).
  apply times_deterministic to Hsquare Hsquare_ground.
  % case of x = 7
  Ha: assert 20 fib (s^7 z) (s^13 z).
  apply fib_deterministic to Ha Hfib.
  Hsquare_ground: assert 49 times (s^7 z) (s^7 z) (s^49 z).
  apply times_deterministic to Hsquare Hsquare_ground.
  % case of x = 8
  Ha: assert 30 fib (s^8 z) (s^21 z).
  apply fib_deterministic to Ha Hfib.
  Hsquare_ground: assert 64 times (s^8 z) (s^8 z) (s^64 z).
  apply times_deterministic to Hsquare Hsquare_ground.
  % case of x = 9
  Ha: assert 40 fib (s^9 z) (s^34 z).
  apply fib_deterministic to Ha Hfib.
  Hsquare_ground: assert 81 times (s^9 z) (s^9 z) (s^81 z).
  apply times_deterministic to Hsquare Hsquare_ground.
  % case of x = 10
  Ha: assert 50 fib (s^10 z) (s^55 z).
  apply fib_deterministic to Ha Hfib.
  Hsquare_ground: assert 100 times (s^10 z) (s^10 z) (s^100 z).
  apply times_deterministic to Hsquare Hsquare_ground.
  % case of x = 11
  Ha: assert 60 fib (s^11 z) (s^89 z).
  apply fib_deterministic to Ha Hfib.
  Hsquare_ground: assert 121 times (s^11 z) (s^11 z) (s^121 z).
  apply times_deterministic to Hsquare Hsquare_ground.
  % case of x = 12
  search.
  % case of x >= 13
  H: apply fib_square_above to Hnat Hcs.
  H: apply *H to Hsquare.
  H: apply *H to Hfib.
  Hnat2: apply times_result_nat to Hnat Hnat Hsquare.
  apply lt_irreflexive to Hnat2 H.

%% <-
intros Hcs.
Hcs: case Hcs.
  case Hsquare. search.
  Hsquare_ground: assert times (s z) (s z) (s z).
  apply times_deterministic to Hsquare Hsquare_ground. search.
  Hsquare_ground: assert 144 times (s^12 z) (s^12 z) (s^144 z).
  apply times_deterministic to Hsquare Hsquare_ground. search 144.
```
