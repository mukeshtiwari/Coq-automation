Require Import Coq.PArith.BinPos
  Coq.ZArith.ZArith
  Lia Coq.Arith.Compare_dec.

Module NotReducing.

Require Import Coq.ZArith.Zwf.

Lemma poslt_wf : well_founded Pos.lt.
Proof.
  unfold well_founded.
  assert (forall (x : Z)  a, x = Zpos a -> Acc Pos.lt a).
  intros x. induction (Zwf_well_founded 1 x);
  intros a Hxa. 
  constructor; intros y Hy.
  eapply H0 with (y := Z.pos y).
  unfold Zwf. split; nia.
  reflexivity.
  intros ?. eapply H with (x := Z.pos a).
  reflexivity.
Defined.

Section T.

Fixpoint guard A (R : A -> A -> Prop) (n : nat) (wfR : well_founded R) : well_founded R :=
    match n with
    | 0%nat => wfR
    | S n' => fun x => Acc_intro x (fun y _ => guard A R n' (guard A R n' wfR) y)
    end.

Variable (x y : positive).


Definition bgcd (u v g : positive) (a b c d : Z) : Z * Z * positive.
  Proof.
    revert g a b c d.
    refine ((fix bgcd u v (H : Acc Pos.lt (Pos.add u v)) {struct H} := 
      match u as up, v as vp return (u, v) = (up, vp) -> _ with
      | xH, xH => fun Huv g a b c d => (a, b, Pos.mul g v)
      | xH, xO pv => fun Huv g a b c d => match Z.even c, Z.even d with
        | true, true => bgcd xH pv _ g a b (Z.div c 2) (Z.div d 2)
        | _, _ => bgcd xH pv _ g a b (Z.div (c + Zpos y) 2) (Z.div (d - Zpos x) 2)
        end
      | xH, xI pv => fun Huv g a b c d => bgcd u (Pos.sub v u) _ g a b (Z.sub c a) (Z.sub d b)
      | xO pu, xH => fun Huv g a b c d => match Z.even a, Z.even b with
        | true, true =>  bgcd pu xH _ g (Z.div a 2) (Z.div b 2) c d
        | _, _ =>  bgcd pu xH _ g (Z.div (a + Zpos y) 2) (Z.div (b - Zpos x) 2) c d
        end
      | xO pu, xO pv => fun Huv g a b c d => bgcd pu pv _ (Pos.mul 2 g) a b c d
      | xO pu, xI pv => fun Huv g a b c d =>  match Z.even a, Z.even b with
        | true, true =>  bgcd pu (xI pv) _ g (Z.div a 2) (Z.div b 2) c d
        | _, _ =>  bgcd pu (xI pv) _ g (Z.div (a + Zpos y) 2) (Z.div (b - Zpos x) 2) c d
        end
      | xI pu, xH => fun Huv g a b c d => bgcd (Pos.sub u v) v _ g (Z.sub a c) (Z.sub b d) c d
      | xI pu, xO pv => fun Huv g a b c d => match Z.even c, Z.even d with
        | true, true => bgcd (xI pu) pv _ g a b (Z.div c 2) (Z.div d 2)
        | _, _ => bgcd (xI pu) pv _ g a b (Z.div (c + Zpos y) 2) (Z.div (d - Zpos x) 2)
        end
      | xI pu, xI pv => fun Huv g a b c d => match (pu ?= pv)%positive with
        | Lt => bgcd u (Pos.sub v u) _ g a b (Z.sub c a) (Z.sub d b)
        | Eq => (a, b, Pos.mul g v)
        | Gt => bgcd (Pos.sub u v) v _ g (Z.sub a c) (Z.sub b d) c d
        end
      end eq_refl) u v ((guard _ Pos.lt 100 poslt_wf) (Pos.add u v))); 
      inversion Huv; subst; clear Huv;
      try (apply Acc_inv with (1 := H); nia).
  Defined.

  
End T.


Time Eval compute in bgcd 2234500 485700 2234500 485700 1 1 0 0 1.

End NotReducing.
