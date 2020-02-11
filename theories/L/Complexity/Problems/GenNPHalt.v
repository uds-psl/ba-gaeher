From Undecidability.L Require Import L.
From Undecidability.L.Datatypes Require Import LProd LTerm LBool.
From Undecidability.L.Complexity Require Import NP Synthetic Monotonic.
From Undecidability.L.Functions Require Import Size.

Definition GenNPHalt' : term*nat*nat -> Prop :=
  fun '(s, maxSize, steps (*in unary*)) =>
    exists (c:term), size (enc c) <= maxSize
                /\ exists t, s (enc c) ⇓(<=steps) t.

Definition HaltsOrDiverges : term*nat*nat -> Prop :=
  fun '(s, maxSize, steps (*in unary*)) =>
    closed s /\ forall (c:term), size (enc c) <= maxSize -> ~(exists t, s (enc c) ⇓ t) \/ exists t, s (enc c) ⇓(<=steps) t.

Definition GenNPHalt := restrictBy HaltsOrDiverges GenNPHalt'.

Lemma NPhard_GenNP : NPhard GenNPHalt.
Proof.
  intros X reg__X P Q [(*? ?*) R R__dec (f__Rbal&polyf__Rbal&bounds_f__Rbal&mono_f__Rbal) R__spec].
  destruct R__dec as (t__R&[d__R [comp_d__R] spec_d__R]&poly_t__R&mono_t__R).
  pose (f x := fun c => d__R (x,c)).
  assert (computableTime' f (fun x _ => (1,fun c _ => (t__R (size (enc (x, c))) + 3,tt))));cbn [timeComplexity] in *.
  {intros. subst f. extract. solverec. }
  specialize inOPoly_computable with (1:=polyf__Rbal) as (f__Rbal'&tf__Rbal'&[]&polyf__Rbal'&leq_f__Rbal'&?&?&?).
  specialize inOPoly_computable with (1:=poly_t__R) as (t__R'&tt__R'&[]&poly_t__R'&leq_t__R'&?&?&?).
  pose (g:= fun x => (lam (trueOrDiverge (extT f (enc x) 0)),f__Rbal' (size (enc x)),t__R' (size (enc x) + f__Rbal' (size (enc x))+4)+9)).
  apply reducesPolyMO_intro with (f:= g);cbn [fst snd]. 
  -unfold g. evar (f':nat -> nat). [f']:refine (fun x => _).
   eexists (fun x => f' x). 
   +exists. extract.
    recRel_prettify2. generalize (size (enc x)). intro. unfold f'. reflexivity. 
   +subst f'. cbn beta. smpl_inO. all:eapply inOPoly_comp. all:smpl_inO.
   +subst f'. cbn beta. smpl_inO.
   +eexists (fun x => _). repeat apply conj.
    *intros. 
     repeat (setoid_rewrite -> size_prod;cbn[fst snd]).
     rewrite !size_nat_enc,!size_term_enc. cbn [size]. 
     generalize (size (enc x)). intros. reflexivity.
    *smpl_inO. all:eapply inOPoly_comp. all:smpl_inO.
    *smpl_inO.
  -intros x x__valid. remember (g x) as x0 eqn:eqx0. destruct x0 as ((t0,maxSize0),steps0).
   unfold g in eqx0. injection eqx0. intros Hx0 Hsize0 Hsteps0. clear eqx0.
   rewrite R__spec. 2:easy. cbn [GenNPHalt restrictBy fst snd].
   unfold HaltsOrDiverges,GenNPHalt'.
   evar (c0 : nat).
   assert (Ht0 : forall c, size (enc c) <= maxSize0 -> t0 (enc c) >(<= c0) trueOrDiverge (enc (f x c))).
   {intros c Hc. subst t0. eapply le_redLe_proper. 2,3:reflexivity. 2:Lsimpl.
    cbn [fst snd]. ring_simplify.
    rewrite size_prod. cbn [fst snd].
    hnf in mono_t__R;erewrite mono_t__R. rewrite leq_t__R'.
    2:now rewrite Hc. 
    unfold c0. reflexivity.
   }
   unshelve eapply (_ : forall (A B : Prop), A -> (A -> B) -> A /\ B). tauto. 
   +split. now subst t0;Lproc.
    intros c H'. specialize (Ht0 c).
    destruct (f x c) eqn:eqfxc.
    *right. eexists. eapply le_evalLe_proper. 2,3:reflexivity. 2:now Lsimpl.
     unfold c0. subst steps0. ring_simplify. 
     subst maxSize0. nia. 
    *left. intros [? Rc].
     apply Ht0 in H'. eapply redLe_star_subrelation in H'. rewrite H' in Rc.
     eapply trueOrDiverge_eval in Rc. easy.    
   +intros [_ Hc]. split.
    *intros (c&H'). specialize (spec_d__R (x,c) x__valid). cbn [fst snd] in *.
     exists c. split. 
     --rewrite bounds_f__Rbal. 2:eassumption. subst;easy.
     --exists I.
       unshelve eassert (Hc'' := Ht0 _ _). 2:{rewrite bounds_f__Rbal. 2:easy. subst maxSize0. now apply leq_f__Rbal'. }
       eapply le_evalLe_proper. 2,3:reflexivity.
       2:{Lsimpl. unfold f. rewrite (proj1 spec_d__R). 2:easy. Lsimpl. }
       subst steps0 c0. cbn beta. ring_simplify. subst maxSize0. nia.
    *intros (c&size__c&?&R').    
     exists c. specialize (spec_d__R (x,c)). cbn in spec_d__R. rewrite spec_d__R. 2:easy. 
     eapply trueOrDiverge_eval with (t:=x0).
     eapply equiv_eval_proper. 2:reflexivity.
     {unfold f in Ht0. specialize (Ht0 _ size__c). apply redLe_star_subrelation in  Ht0.  rewrite <- Ht0.
      symmetry. apply star_equiv_subrelation. eapply redLe_star_subrelation. apply R'.
     }
     apply eval_refl. now destruct R'.
Qed.
