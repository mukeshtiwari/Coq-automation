
(* https://sympa.inria.fr/sympa/arc/coq-club/2007-07/msg00013.html
   https://coq-club.inria.narkive.com/gO2dnKc4/well-founded-recursion-stuck-on-opaque-proofs
   https://sympa.inria.fr/sympa/arc/coq-club/2013-09/msg00034.html?ticket=ST-272822-JjlPeYflOHbYh07SIzDGXuXTxLk-cas.inria.fr
*)

  Fixpoint guard A (R : A -> A -> Prop) (n : nat) (wfR : well_founded R) : well_founded R :=
    match n with
    | 0%nat => wfR
    | S n' => fun x => Acc_intro x (fun y _ => guard A R n' (guard A R n' wfR) y)
    end.


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
    + apply N.ltb_lt in Hnp; exact Hnp.
    + apply (nmod_256 up).
    + eapply Acc_inv with (x := t). exact H.
      apply N.ltb_ge in Hnp.
      eapply N_eq_gt with (up := up); auto. 
  Defined.

  Eval compute in length_byte_list 256.
