Require Import Coq.PArith.BinPos
  Coq.ZArith.ZArith
  Lia Coq.Arith.Compare_dec.


Module Reducing.
Local Open Scope Z_scope.

Section wf_proof.

  Let f (c : Z) (a : Z) := Z.abs_nat (a - c).

  Definition zwf (c : Z) (x y : Z) := (f c x < f c y)%nat.

  Lemma zwf_well_founded (c : Z) : well_founded (zwf c).
  Proof.
    exact (well_founded_ltof Z (f c)).
  Defined.
    
  Lemma pos_acc : forall x a, Zpos a <= x -> Acc Pos.lt a.
  Proof.
    intro x.
    induction (zwf_well_founded 1 x) as [z Hz IHz].
    intros ? Hxa.
    constructor; intros y Hy.
    eapply IHz with (y := Z.pos y).
    unfold zwf. clear Hz; clear IHz.
    apply Zabs_nat_lt.
    split; nia.
    reflexivity.
  Defined.


  Lemma poslt_wf : well_founded Pos.lt.
  Proof.
    red; intros ?.
    eapply pos_acc.
    instantiate (1 := Z.pos a).
    reflexivity.
  Defined. 

  About poslt_wf.

End wf_proof.

Section Extgcd.

  
  Variable (x y : positive).

  Definition poseven (a : positive) : bool :=
  match a with
  | xO _ => true
  | _ => false
  end.

  Lemma poseven_div : forall p, true = poseven p -> (Pos.div2 p < p)%positive.
  Proof.
  induction p; simpl; intro H; try (inversion H).
  nia.
  Qed.

  Definition binary_gcd (u v g : positive) (a b c d : Z) : Z * Z * positive.
  Proof.
    revert g a b c d.
    refine ((fix binary_gcd u v (H : Acc Pos.lt (Pos.add u v)) { struct H } := _) u v (poslt_wf _)).
    intros g a b c d.
    case_eq (poseven u); case_eq (poseven v); intros Hv Hu.
    + refine (binary_gcd (Pos.div2 u) (Pos.div2 v) _ (Pos.mul 2 g) a b c d).
      now apply Acc_inv with (1 := H), Pos.add_lt_mono; apply poseven_div.
    + refine (match Z.even a, Z.even b with
        | true, true => binary_gcd (Pos.div2 u) v _ g (Z.div a 2) (Z.div b 2) c d
        | _   , _    => binary_gcd (Pos.div2 u) v _ g (Z.div (a + Zpos y) 2) (Z.div (b - Zpos x) 2) c d
      end); now apply Acc_inv with (1 := H), Pos.add_lt_mono_r, poseven_div.
    + refine (match Z.even c, Z.even d with
        | true, true => binary_gcd u (Pos.div2 v) _ g a b (Z.div c 2) (Z.div d 2)
        | _   , _    => binary_gcd u (Pos.div2 v) _ g a b (Z.div (c + Zpos y) 2) (Z.div (d - Zpos x) 2)
      end); now apply Acc_inv with (1 := H), Pos.add_lt_mono_l, poseven_div.
    + case_eq (u ?= v)%positive; intros Huv.
      * exact (a, b, Pos.mul g v).
      * refine (binary_gcd u (Pos.sub v u) _ g a b (Z.sub c a) (Z.sub d b)).
        apply Acc_inv with (1 := H).
        rewrite Pos.compare_lt_iff in Huv; nia.
      * refine (binary_gcd (Pos.sub u v) v _ g (Z.sub a c) (Z.sub b d) c d).
        apply Acc_inv with (1 := H).
        rewrite Pos.compare_gt_iff in Huv; nia.
  Defined.
End Extgcd.

Time Eval vm_compute in binary_gcd 22345 485 22345 485 1 1 0 0 1.

Section Onemore. 

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
        end eq_refl) u v (poslt_wf _ )); inversion Huv; subst; clear Huv;
        try (apply Acc_inv with (1 := H); nia).
    Defined.

End Onemore.

Time Eval vm_compute in bgcd 22345 485 22345 485 1 1 0 0 1.

  Fixpoint bin_gcd (n : nat) (x y : positive) (u v g : positive) (a b c d : Z) : Z * Z * positive :=
    match n with 
    | 0%nat => (a, b, Pos.mul g v)
    | S n' => 
        match poseven u, poseven v with
        | true, true => bin_gcd n' x y (Pos.div2 u) (Pos.div2 v) (Pos.mul 2 g) a b c d
        | true, false => 
          match Z.even a, Z.even b with
          | true, true =>  bin_gcd n' x y (Pos.div2 u) v g (Z.div a 2) (Z.div b 2) c d
          | _, _ =>  bin_gcd n' x y (Pos.div2 u) v g (Z.div (a + Zpos y) 2) (Z.div (b - Zpos x) 2) c d
          end
        | false, true => 
          match Z.even c, Z.even d with
          | true, true => bin_gcd n' x y u (Pos.div2 v) g a b (Z.div c 2) (Z.div d 2)
          | _, _ => bin_gcd n' x y u (Pos.div2 v) g a b (Z.div (c + Zpos y) 2) (Z.div (d - Zpos x) 2)
          end
        | false, false => 
            match (u ?= v)%positive with
            | Lt => bin_gcd n' x y u (Pos.sub v u) g a b (Z.sub c a) (Z.sub d b)
            | Eq => (a, b, Pos.mul g v)
            | Gt => bin_gcd n' x y (Pos.sub u v) v g (Z.sub a c) (Z.sub b d) c d
            end
        end
    end.

    Time Eval vm_compute in bin_gcd 100 22345 485 22345 485 1 1 0 0 1.
    Definition binary_extended_gcd (a b : positive) := 
      bin_gcd (2 * (Pos.size_nat a + Pos.size_nat b + 2)) a b a b 1 1 0 0 1.

    Time Eval compute in binary_extended_gcd 9873492734 6434423.

End Reducing.

Module NotReducing.

Require Import Coq.NArith.BinNat.
Require Import Coq.Program.Wf.
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

About poslt_wf.
About Reducing.poslt_wf.
Section T.

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
      end eq_refl) u v (poslt_wf _ )); inversion Huv; subst; clear Huv;
      try (apply Acc_inv with (1 := H); nia).
  Defined.

  About bgcd.
  About poslt_wf.
End T.



(* This one does not reduce  to any value *)
Time Eval compute in bgcd 2 3 2 3 1 1 0 0 1.

End NotReducing.


