Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
From QuickChick Require Import QuickChick.
From Hammer Require Import Hammer Reconstr.

Global Instance Dec_iff {P Q} {H : Dec P} {I : Dec Q} : Dec (P <-> Q).
Proof.
  constructor. unfold ssrbool.decidable.
  destruct H as [D]; destruct D;
    destruct I as [D]; destruct D; hammer.
Defined.

Definition E := nat.
Definition eeq : forall (e1 e2 : E), {e1 = e2} + {e1 <> e2} := Nat.eq_dec.

Definition set : Type -> Type := list.
Definition contains (A : set E) (e : E) : Prop := List.In e A.
Definition empty_set : set E := nil.
Definition singleton_set (e : E) : set E := List.cons e empty_set.
Definition add_element (e : E) (s : set E) : set E :=
  if in_dec eeq e s then s else e :: s.

Definition union (A B : set E) : set E :=
  fold_left (fun s e => add_element e s) A B.

Definition intersection (A B : set E) : set E :=
  fold_left (fun s e => if in_dec eeq e B then e :: s else s) A empty_set.

(*
Conjecture empty_set_spec : forall (x : E), contains empty_set x <-> False.
QuickChick empty_set_spec.

Error:
Unable to satisfy the following constraints:

?arg_2 : "Checkable (forall x : E, contains empty_set x <-> False)" *)

Conjecture singleton_set_spec: forall (x y: E),
    contains (singleton_set y) x <-> x = y.
QuickChick singleton_set_spec.

Conjecture union_spec: forall (x: E) (A B: set E),
    contains (union A B) x <-> contains A x \/ contains B x.
QuickCheck union_spec.


Conjecture nat_add : forall n m, n + m = m + n .
QuickCheck nat_add.

Conjecture nat_add_fail : forall n m, n + m = m.
QuickCheck nat_add_fail.

