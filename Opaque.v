
(* https://sympa.inria.fr/sympa/arc/coq-club/2007-07/msg00013.html
   https://coq-club.inria.narkive.com/gO2dnKc4/well-founded-recursion-stuck-on-opaque-proofs
   https://sympa.inria.fr/sympa/arc/coq-club/2013-09/msg00034.html?ticket=ST-272822-JjlPeYflOHbYh07SIzDGXuXTxLk-cas.inria.fr
*)

From Coq Require Import Arith Utf8 Psatz
  Peano NArith Strings.Byte NArith.

  Local Open Scope N_scope.


  Fixpoint guard A (R : A -> A -> Prop) (n : nat) (wfR : well_founded R) : well_founded R :=
    match n with
    | 0%nat => wfR
    | S n' => fun x => Acc_intro x (fun y _ => guard A R n' (guard A R n' wfR) y)
    end.


  Definition np_total (np : N):  (np <? 256 = true) ->  byte.
  Proof.
    intros H.
    pose proof of_N_None_iff np as Hn.
    destruct (of_N np) as [b | ].
    + exact b.
    + exfalso; abstract (apply N.ltb_lt in H;
        intuition nia). 
  Defined.

  Lemma nmod_256 : forall np, np mod 256 < 256.
  Proof. 
    intros; eapply N.mod_lt; intro H;
    inversion H.
  Qed. 


  Lemma N_eq_gt : forall up t : N, 256 <= up -> t = up / 256 -> 0 <=  t / 256 < t.
  Proof.
    intros up t Hup Ht.
    split. 
    apply N.le_0_l.
    apply N.div_lt_upper_bound. 
    nia.
    (* I know that 1 <= t *)
    assert (Hot: 1 <= t).
    rewrite Ht.
    apply N.div_le_lower_bound.
    nia.
    simpl. exact Hup. nia.
  Qed.
  
  Definition length_byte_list (np : N) : list byte.
  Proof.
    refine ((fix length_byte_list up (H: Acc (fun x y => 0 <= x < y) (N.div up 256)) {struct H}:= 
      match (up <? 256) as upp return _ = upp -> _ with
      | true => fun Hnp => List.cons (np_total up _) List.nil
      | false => fun Hnp => 
        let r := N.modulo up 256 in 
        let t := N.div up 256 in 
        List.cons (np_total r _) (length_byte_list t _)
      end eq_refl
    ) np (guard _ (fun x y => 0 <= x < y) 100 (N.lt_wf 0) (N.div np 256))).
    + exact Hnp.
    + apply N.ltb_lt. apply (nmod_256 up).
    + eapply Acc_inv with (x := t). exact H.
      apply N.ltb_ge in Hnp.
      eapply N_eq_gt with (up := up); auto. 
  Defined.

  Eval compute in length_byte_list 256.
  
  
  (* So it seems we can compute without guard condition as well *)
  
  Definition length_byte_list_without_guard : N -> list byte.
  Proof.
    intro np.
    cut (Acc lt (N.to_nat np));
    [revert np |].
    +
      refine(fix length_byte_list_without_guard np (acc : Acc lt (N.to_nat np))
        {struct acc} := 
      match acc with 
      | Acc_intro _ f => 
        match (np <? 256) as npp 
          return _ = npp -> _ 
        with
        | true => fun Ha => List.cons (np_total np Ha) List.nil
        | false => fun Ha => 
            let r := N.modulo np 256 in 
            let t := N.div np 256 in 
            List.cons (np_total r _) (length_byte_list_without_guard t _)
        end eq_refl
      end).
      ++
        apply N.ltb_lt, (nmod_256 np).
      ++
        apply N.ltb_ge in Ha.
        assert (Hc : (N.to_nat t < N.to_nat np)%nat).
        unfold t. rewrite N2Nat.inj_div.
        eapply Nat.div_lt; try abstract nia.
        exact (f (N.to_nat t) Hc).
    +
      apply lt_wf.
  Defined.

  Eval compute in length_byte_list_without_guard 3723.
