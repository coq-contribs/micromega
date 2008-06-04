Require  Import ZArith.
Require Import Micromegatac.

Open Scope Z_scope.

Goal (forall x y n,
  ( ~ x < n /\ x <= n /\ 2 * y = x*(x+1) -> 2 * y = n*(n+1))
  /\
  (x < n /\ x <= n /\ 2 * y = x * (x+1) -> x + 1 <= n /\ 2 *(x+1+y) = (x+1)*(x+2))).
Proof.
  intros.
  micromega Z.
Qed.
