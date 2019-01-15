From Hammer Require Import Hammer Reconstr.
Require Import Coq.ZArith.ZArith.
Open Scope Z.

Set Hammer Eprover.
Set Hammer Vampire.
Set Hammer Z3.
Set Hammer CVC4.
Lemma addition_commute : forall n m, n + m = m + n.
Proof.
  hammer.
Qed.


Lemma max_of_three : forall n m p, max n (max m p) = max (max n m) p.
  hammer.
Qed.

Fixpoint even (n : nat) : bool :=
  match n with
  | O => true
  | S O => false
  | (S (S n')) => even n'
  end.

Lemma even_256 : even 256 = true.
  hammer.
Qed.


Inductive Evenn : nat -> Prop :=
| Bcase : Evenn O
| Ccase n : Evenn n -> Evenn (S (S n)).

Lemma even_ind : Evenn 10.
  hammer.
Qed.

Lemma connect_even_Even :
  forall n, Evenn n <-> even n = true.
Proof.
  (* Hammer is not able to solve this goal *)
  split; intros. 
  induction H; scrush.
  generalize dependent n.
  refine (fix Fn n :=
            match n with
            | O => fun H => _
            | S O => fun H => _
            | S (S n') => fun H => _
            end).
  constructor.
  inversion H.
  cbn in H.
  constructor 2. apply Fn.
  auto.
Qed.

Lemma nat_even_odd :
  forall (n : nat), Nat.Odd n \/ Nat.Even n.
Proof.
  hammer.
Qed.

Lemma lem_pow : forall n : nat, (3 * 3 ^ n)%nat = (3 ^ (n + 1))%nat.
  hammer.
Qed.

Lemma lem_lst_1 : forall (A : Type) (l l' : list A), List.NoDup (l ++ l') -> List.NoDup l.
Proof.
  (* The hammer can't do induction. If induction is necessary to carry out the
  proof, then one needs to start the induction manually. *)
  induction l'.
  hammer. Undo.
  Reconstr.reasy (@Coq.Lists.List.app_nil_end) Reconstr.Empty.
  hammer. Undo.
  Reconstr.reasy (@Coq.Lists.List.NoDup_remove_1) Reconstr.Empty.
Qed.

Lemma NoDup_remove_1
     : forall (A : Type) (a : A) (l' l : list A),
       List.NoDup (l ++ a :: l') ->
       ~ List.In a (l ++ l') /\ List.NoDup (l ++ l') /\ List.NoDup l.
Proof.
  Reconstr.rcrush (@Coq.Lists.List.NoDup_remove, @lem_lst_1) Reconstr.Empty.
Qed.
