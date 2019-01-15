From Hammer Require Import Hammer Reconstr.
Require Import Coq.ZArith.ZArith.
Open Scope Z.

Lemma addition_commute : forall n m, n + m = m + n.
Proof.
  hammer.
Qed.


Lemma max_of_three : forall n m p, max n (max m p) = max (max n m) p.
  hammer.
Qed.
