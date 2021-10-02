Require Import Coq.PArith.BinPos
  Coq.ZArith.ZArith
  Lia Coq.Arith.Compare_dec.

 
Local Open Scope Z_scope.

(* This code is taken from the library but it was opaque so I made it transparent. Defined and Z_le_gt_dec *)
Section wf_proof.

  Definition Zwf (c x y:Z) := c <= y /\ x < y.
  (** The proof of well-foundness is classic: we do the proof by induction
      on a measure in nat, which is here [|x-c|] *)

  Let f (c : Z) (z : Z) := Z.abs_nat (z - c).

  Lemma zwf_well_founded (c : Z) : well_founded (Zwf c).
    red; intros.
    assert (forall (n:nat) (a:Z), (f c a < n)%nat \/ a < c -> Acc (Zwf c) a).
    clear a. simple induction n; intros.
  (** n= 0 *)
    case H; intros.
    lia.
    apply Acc_intro; unfold Zwf; intros.
    lia.
  (** inductive case *)
    case H0; clear H0; intro; auto.
    apply Acc_intro; intros.
    apply H.
    unfold Zwf in H1.
    case (Z_le_gt_dec c y); intro. 2: lia.
    left.
    apply lt_le_trans with (f c a); auto with arith.
    unfold f.
    lia.
    apply (H (S (f c a))); auto.
  Defined.





  Lemma poslt_wf : well_founded Pos.lt.
  Proof.
    unfold well_founded.
    assert (forall x a, x = Zpos a -> Acc Pos.lt a).
    intros x. induction (zwf_well_founded 1 x).
    Locate zwf_well_founded.
    intros ? Hxa. subst x.
    constructor; intros y Hy.
    eapply H0 with (y := Zpos y); trivial.
    split; auto with zarith.
    intros. apply H with (Zpos a).
    exact eq_refl.
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
  Require Extraction. Extraction  bgcd.
      (* This is the fastest one amongst all becuase there is no proof, but it runs on fuel. 
       Now the challenge is to prove that the fuel below is sufficient to compute any gcd *)
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

    Definition binary_extended_gcd (a b : positive) := 
      bin_gcd (2 * (Pos.size_nat a + Pos.size_nat b + 2)) a b a b 1 1 0 0 1.

    Eval compute in binary_extended_gcd 9873492734 6434423.

        
        

