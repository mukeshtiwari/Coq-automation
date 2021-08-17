Require Import 
  Coq.setoid_ring.Ring_theory
  Coq.Vectors.Vector Setoid Morphisms BinPos BinNat
  CoLoR.Util.Vector.VecUtil Lia
  Coq.ZArith.ZArith.
  
  Set Implicit Arguments.

Section General_Matrix_Multiplication.
  
  Variable R : Type.
  Variable (rO rI : R) (radd rmul : R->R->R).
  Variable srt : semi_ring_theory rO rI radd rmul (@eq R).

  Definition matrix m n := vector (vector R n) m.

  Definition get_row {m n : nat} (M : matrix m n) i (ip : i < m) := 
    Vnth M ip.

  Definition get_col {m n : nat} (M : matrix m n) i (ip : i < n) := 
    Vmap (fun v => Vnth v ip) M.

  Definition get_elem {m n : nat} (M : matrix m n) i j (ip : i < m) (jp : j < n) :=
    Vnth (get_row M ip) jp.
  
  Definition vnth : forall (n : nat), vector R n -> forall (i : nat), i < n -> R.
  Proof.
    refine (fix IHn n := 
     match n as np return n = np -> vector R np -> forall i, i < np -> R with
     | 0 => fun Hn v i Hi => _ 
     | S n' => fun Hn v i Hi => 
        match i as ip return i = _ -> R with
        | 0 => fun Hip => hd v
        | S i' => fun Hip => _ 
        end eq_refl
     end eq_refl).
     ++ abstract lia.
     ++ subst. apply Lt.lt_S_n in Hi.
        exact (IHn n' (tl v) i' Hi).
  Defined.

  
Definition Matrix (m n : nat) := forall i, i < m -> forall j, j < n -> R.


Lemma f : forall m n, Matrix m n -> (Fin.t m -> Fin.t n -> R).
Proof.
  induction m.
  + intros ? Hm Hf1 Hf2.
    inversion Hf1. 
  + (* m = S m*)
    destruct n.
    ++ intros Hm Hf1 Hf2. 
       inversion Hf2.
    ++ intros Hm Hf1 Hf2.
       remember Hf1 as Hf1'. 
       remember Hf2 as Hf2'.

       (* destruct both. 
        1. F1, F1 
        2. F1, FS
        3. FS, F1.
        4. FS, FS *)

        destruct Hf1, Hf2.
        +++ assert (Hl1: 0 < S n0) by abstract lia. 
            assert (Hl2: 0 < S n1) by abstract lia. 
            exact (Hm 0 Hl1 0 Hl2).
        +++ assert (Hl1: 0 < S n0) by abstract lia.
            assert (Hl2: n1 < S n1) by abstract lia. 
            exact (Hm 0 Hl1 n1 Hl2).
        +++ assert (Hl1: n0 < S n0) by abstract  lia.
            assert (Hl2 : 0 < S n1) by abstract lia.
            exact (Hm n0 Hl1 0 Hl2).
        +++ assert (Hl1: n0 < S n0) by abstract lia.
            assert (Hl2: n1 < S n1) by abstract lia.
            exact (Hm n0 Hl1 n1 Hl2).
            
Defined.

Theorem fin_cast : forall m n, m = n -> Fin.t m -> Fin.t n.
Proof.
  intros ? ? Hm v.
  refine  
    match Hm in _ = n return Fin.t n with
    | eq_refl => v
    end.
Defined. 

Lemma fin_sig : forall m, Fin.t m -> sig (fun i => i < m). (* {i | i < m}*)
Proof.
  refine (fix fn m := 
      match m : nat as mt return m = mt -> Fin.t mt -> sig (fun i => i < mt) with
      | 0 => _ 
      | S m' => fun Hm Hf => _
      end eq_refl).
    + intros Hm Hf. 
      inversion Hf. 
    + remember Hf as Hf'.
      destruct Hf.
      ++ exists 0. 
         apply Nat.lt_0_succ.
      ++ destruct m. 
        +++ inversion Hm.
        +++ inversion Hm; clear Hm.
            symmetry in H0.
            pose proof (@fin_cast n m H0 Hf).
            destruct (fn m H) as [hm Hm].
            exists (S hm).      
            apply  lt_n_S. 
            rewrite H0. exact Hm.
  Defined.

  Eval compute in (fin_sig (Fin.FS (Fin.FS Fin.F1))).
  
  Lemma sig_fin : forall m, sig (fun i => i < m) -> Fin.t m.
  Proof. 
    induction m.
    + intros [i Hi]. 
      abstract lia.
    + intros [i Hi].
      ++ destruct i.
        +++ exact (Fin.F1).
        +++ assert (Ht : i < m) by abstract lia.
            assert (Hv : {i | i < m}). exists i.
            abstract lia.
            exact (Fin.FS (IHm Hv)).
  Defined.


        
      
  




Lemma g : forall m n, (Fin.t m -> Fin.t n -> R) -> Matrix m n. 
Proof. 
Admitted.

              
Theorem pf : forall m n (u : Matrix m n), g (f u) = u.
Proof. 
Admitted.  
            
        
        




    



End General_Matrix_Multiplication.

