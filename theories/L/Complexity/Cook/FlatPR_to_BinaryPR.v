From PslBase Require Import Base. 
From PslBase Require Import Vectors.Vectors. 
From Undecidability.L.Complexity.Cook Require Import Prelim UniformHomomorphisms BinaryPR FlatPR PR_to_BinaryPR. 
Require Import Lia.

(** Reduction of FlatPR to BinaryPR *)
(*logically, we reduce FlatPR to PR and use the reduction of PR to BinaryPR *)
(*but in order to make the reduction extractable, we give a shortcut reduction which produces instances which are the same up to syntax (like reordering)*)

Section fixInstanceA. 
  (*we first do the reduction for well-formed instances satisfying the syntactic requirements *)

  Variable (fpr : FlatPR). 

  Notation Sigma := (Sigma fpr).
  Notation offset := (offset fpr).
  Notation width := (width fpr).
  Notation init := (init fpr).
  Notation windows := (windows fpr).
  Notation final := (final fpr).
  Notation steps := (steps fpr). 

  Context (A : FlatPR_wellformed fpr). 
  Context (B : isValidFlattening fpr). 
  Context (A1 : Sigma > 0). (*instances without this property are trivial no instances *)

  (*we use the hNat base homomorphism from the PR reduction *)
  Definition hflat := canonicalHom (hNat Sigma).

  Definition hoffset := Sigma * offset. 
  Definition hwidth := Sigma * width. 
  Definition hinit := hflat init.
  Definition hwindow win := match win with Build_PRWin prem conc => Build_PRWin (hflat prem) (hflat conc) end.
  Definition hwindows := map hwindow windows. 
  Definition hfinal := map hflat final. 
  Definition hsteps := steps. 

  Definition hBinaryPR := @BinaryPR.Build_BinaryPR hoffset hwidth hinit hwindows hfinal hsteps. 

  (*We show that if fpr is the flattening of a PR instance pr, then the produced BinaryPR instances are equivalent up to reordering of windows and final strings *)

  Variable (pr : PR). 
  Variable (isFlattening : isFlatPROf fpr pr). 

  Definition finhBinaryPR := PR_to_BinaryPR.hBinaryPR pr.

  (*agreement of produced lists, windows, ... *)
  Lemma isFlatListOf_hom_agree l L : isFlatListOf l L -> hflat l = @h pr L.  
  Proof. 
    destruct isFlattening. 
    intros. rewrite H. unfold h, PR_homomorphisms.h. 
    unfold h', hflat. rewrite <- HSigma. 
    unfold canonicalHom. now rewrite map_map. 
  Qed. 

  Lemma isFlatPRWinOf_hom_agree w W : isFlatPRWinOf w W -> hwindow w = PR_homomorphisms.hwindow (@h' pr) W.
  Proof. 
    intros. destruct w, W. cbn. 
    erewrite isFlatListOf_hom_agree; [ | apply H]. 
    erewrite isFlatListOf_hom_agree; [ | apply H]. 
    easy.
  Qed. 

  Lemma isFlatWindowsOf_hom_agree: hwindows === PR_homomorphisms.hwindows (@h' pr).  
  Proof. 
    split; intros a H;
    [unfold hwindows in H | unfold PR_homomorphisms.hwindows in H]; apply in_map_iff in H as (win & <- & H); apply isFlattening in H as (win' & H & H1); 
      apply isFlatPRWinOf_hom_agree in H1; apply in_map_iff; eauto.  
  Qed. 

  Lemma isFlatFinalOf_hom_agree: hfinal === PR_homomorphisms.hfinal (@h' pr).
  Proof. 
    split; intros a H; [unfold hfinal in H | unfold PR_homomorphisms.hfinal in H]; 
    apply in_map_iff in H as (subs & <- & H); apply isFlattening in H as (subs' & H & H1);
      apply isFlatListOf_hom_agree in H1; apply in_map_iff; eauto. 
  Qed. 

  (*equivalence of well-formedness *)
  Lemma BinaryPR_instances_wf_equivalent : BinaryPR_wellformed finhBinaryPR <-> BinaryPR_wellformed hBinaryPR. 
  Proof. 
    destruct isFlattening. 
    unfold BinaryPR_wellformed. cbn. unfold PR_homomorphisms.hwidth, PR_homomorphisms.hoffset, hwidth, hoffset.  
    rewrite <- !HSigma, <- !HWidth, <- !HOffset. 
    split; intros (H1 & H2 & H3 & H4 &H5 & H6); repeat match goal with [ |- _ /\ _] => split end; try easy.
    - unfold hinit. erewrite isFlatListOf_hom_agree; [ | easy]. apply H4. 
    - intros. rewrite (isFlatWindowsOf_hom_agree) in H. easy.
    - unfold hinit. erewrite isFlatListOf_hom_agree; [ | easy]. apply H6. 
    - unfold hinit in H4. erewrite isFlatListOf_hom_agree in H4; [ | easy]. apply H4. 
    - intros. rewrite <- (isFlatWindowsOf_hom_agree) in H. easy.
    - unfold hinit in H6. erewrite isFlatListOf_hom_agree in H6; [ | easy]. apply H6. 
  Qed. 

  (*now the instances are in fact equivalent *)
  Lemma BinaryPR_instances_equivalent : BinaryPRLang finhBinaryPR <-> BinaryPRLang hBinaryPR. 
  Proof. 
    unfold BinaryPRLang. destruct isFlattening. 
    cbn. unfold PR_homomorphisms.hwidth, PR_homomorphisms.hoffset, hwidth, hoffset, PR_homomorphisms.hsteps, hsteps.  
    rewrite <- !HSigma, <- !HWidth, <- !HOffset, <- !HSteps. 
    unfold hinit, PR_homomorphisms.hinit. setoid_rewrite isFlatListOf_hom_agree; [ | easy | easy].

    split; intros (Hwf & sf & H1 & H2 );
    (split; [ apply BinaryPR_instances_wf_equivalent, Hwf| exists sf; split ]).
    - eapply relpower_congruent. 2: apply H1. intros. eapply valid_windows_equivalent. 
      apply isFlatWindowsOf_hom_agree.
    - eapply satFinal_final_equivalent. 2: apply H2. apply isFlatFinalOf_hom_agree. 
    - eapply relpower_congruent. 2: apply H1. intros. eapply valid_windows_equivalent. 
      symmetry. apply isFlatWindowsOf_hom_agree.
    - eapply satFinal_final_equivalent. 2: apply H2. symmetry. apply isFlatFinalOf_hom_agree. 
  Qed. 
End fixInstanceA.

(*as usual, instances not satisfying the syntactic requirements are just mapped to a trivial no instance *)
Definition trivialNoInstance := Build_BinaryPR 0 0 [] [] [] 0. 
Lemma trivialNoInstance_isNoInstance : not (BinaryPRLang trivialNoInstance). 
Proof. 
  intros (H & _). destruct H as (H & _). cbn in H. lia. 
Qed. 

Definition reduction (fpr : FlatPR) :=
  if FlatPR_wf_dec fpr && isValidFlattening_dec fpr then hBinaryPR fpr else trivialNoInstance.

Lemma FlatPR_to_BinaryPR (fpr : FlatPR) : FlatPRLang fpr <-> BinaryPRLang (reduction fpr).  
Proof. 
  split; intros. 
  - destruct H as (H1 & Hwf & H2). 
    unfold reduction. 
    rewrite (proj2 (FlatPR_wf_dec_correct _) H1). 
    rewrite (proj2 (isValidFlattening_dec_correct _) Hwf). 
    specialize (unflattenPR Hwf) as (pr & H3).
    eapply BinaryPR_instances_equivalent; [ apply H3 | ]. 
    apply isFlatPROf_equivalence in H3. 
    enough (PRLang pr). 
    { specialize (PR_to_BinaryPR pr) as H4. unfold PR_to_BinaryPR.reduction in H4. 
      enough (PR_wf_dec pr = true) as H5 by (rewrite H5 in H4; apply H4, H). 
      destruct H as (H & _ & _). apply PR_wf_dec_correct, H.  
    } 
    apply H3; easy.
  - unfold reduction in H. destruct (FlatPR_wf_dec) eqn:H1, (isValidFlattening_dec) eqn:H2. 
    2-4: cbn in H; now apply trivialNoInstance_isNoInstance in H.
    cbn in H. apply isValidFlattening_dec_correct in H2. apply FlatPR_wf_dec_correct in H1. 
    (*we restore an unflattened instance *)
    specialize (unflattenPR H2) as (pr & H3). eapply isFlatPROf_equivalence; [ apply H3 | ]. 
    apply PR_to_BinaryPR. unfold PR_to_BinaryPR.reduction. 
    enough (PR_wf_dec pr = true) as -> by now eapply BinaryPR_instances_equivalent. 
    eapply PR_wf_dec_correct, isFlatPROf_wf_equivalent; easy.
Qed.


(** *extraction *)
From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import  LProd LOptions LBool LLNat LLists.
From Undecidability.L.Complexity Require Import PolyBounds. 

(*repEl *)
Section fixX. 
  Context {X : Type}.
  Context `{H: registered X}. 

  Definition c__repEl2 := 5.
  Definition c__repEl := c__repEl2 + 7.
  Definition repEl_time (n: nat) := (n +1) * c__repEl. 
  Global Instance term_repEl : computableTime' (@repEl X) (fun n _ => (c__repEl2, fun e _ => (repEl_time n, tt))). 
  Proof. 
    extract. solverec. all: unfold repEl_time, c__repEl, c__repEl2; solverec.
  Defined. 

  Lemma repEl_time_mono : monotonic repEl_time. 
  Proof. 
    unfold repEl_time; smpl_inO. 
  Qed. 

  Definition poly__repEl n := (n+1) * c__repEl.
  Lemma repEl_time_bound n : repEl_time n <= poly__repEl (size (enc n)). 
  Proof. 
    unfold repEl_time, poly__repEl. replace_le n with (size (enc n)) by (apply size_nat_enc_r) at 1. lia. 
  Qed. 
  Lemma repEl_poly : monotonic poly__repEl /\ inOPoly poly__repEl. 
  Proof. 
    unfold poly__repEl; split; smpl_inO. 
  Qed. 
End fixX. 

(*hNat *)
Definition c__hNat := 2 * (c__leb2 + 2 * c__repEl2 + 82).
Definition hNat_time sig n := (leb_time (S n) sig + repEl_time sig + sig + 1) * c__hNat. 
Instance term_hNat : computableTime' hNat (fun sig _ => (1, fun n _ => (hNat_time sig n, tt))). 
Proof. 
  specialize (repEl_time_mono) as H1. unfold monotonic in H1. 
  extract. solverec. 
  - setoid_rewrite Nat.le_min_r at 2. rewrite Nat.mul_1_r. rewrite repEl_length. 
    apply leb_iff in H. rewrite H1 with (x' := x) by lia. setoid_rewrite H1 with (x' := x) at 2. 2: lia. 
    rewrite Nat.le_min_l. 
    unfold hNat_time, c__hNat. cbn[Nat.add]. nia. 
  - cbn[Nat.add]. unfold hNat_time, c__hNat. apply Nat.leb_gt in H. 
    unfold repEl_time. nia. 
Qed. 

Definition c__hNatBound := (c__leb + 1) * (c__hNat + 1).
Definition poly__hNat n := (poly__repEl n + n + 1) * c__hNatBound.
Lemma hNat_time_bound sig n: hNat_time sig n <= poly__hNat (size (enc sig)). 
Proof. 
  unfold hNat_time. rewrite leb_time_bound_r. 
  unfold poly__hNat, c__hNatBound. rewrite repEl_time_bound. rewrite size_nat_enc_r with (n := sig) at 3.
  leq_crossout. 
Qed. 
Lemma hNat_poly : monotonic poly__hNat /\ inOPoly poly__hNat. 
Proof.
  unfold poly__hNat; split; smpl_inO; apply repEl_poly. 
Qed. 

(*concat *)
Section concat_fixX. 
  Context {X : Type}.
  Context `{registered X}.
  
  Definition c__concat := 19.
  Definition concat_time (l : list (list X)) := fold_right (fun l acc => c__concat * (|l|) + acc + c__concat) c__concat l.
  Global Instance term_concat : computableTime' (@concat X) (fun l _ => (concat_time l, tt)). 
  Proof. 
    extract. unfold concat_time, c__concat. solverec. 
  Qed. 
  
  Definition poly__concat n := (n + 1) * c__concat.
  Lemma concat_time_bound l : concat_time l <= poly__concat (size (enc l)). 
  Proof. 
    unfold concat_time. induction l; cbn -[Nat.add Nat.mul].
    - unfold poly__concat. nia. 
    - rewrite IHl. unfold poly__concat. rewrite list_size_cons. rewrite list_size_length. nia.
  Qed. 
  Lemma concat_poly : monotonic poly__concat /\ inOPoly poly__concat. 
  Proof. 
    split; unfold poly__concat; smpl_inO. 
  Qed. 
End concat_fixX. 

(*hflat *)
Definition c__hflat := c__Sigma + 3. 
Definition hflat_time (fpr : FlatPR) (l : list nat) := map_time (fun m => hNat_time (Sigma fpr) m) l + concat_time (map (hNat (Sigma fpr)) l) + c__hflat.
Instance term_hflat : computableTime' hflat (fun fpr _ => (1, fun l _ => (hflat_time fpr l, tt))).  
Proof. 
  unfold hflat. unfold canonicalHom. extract. solverec. 
  unfold hflat_time, c__hflat. solverec. 
Qed. 

Definition c__hNatSize := 9.
Lemma hNat_size_bound sig n: size (enc (hNat sig n)) <= (sig + 1) * c__hNatSize. 
Proof. 
  specialize (list_size_of_el (l := (hNat sig n)) (k := 4)) as H1.  
  rewrite H1. 2: { intros. apply size_bool. }
  rewrite hNat_length. unfold c__hNatSize. lia. 
Qed. 

Lemma map_hNat_size_bound sig l : size (enc (map (hNat sig) l)) <= (|l|) * (sig + 1) * c__hNatSize + 5 * (|l|) + 4. 
Proof. 
  erewrite list_size_of_el. 
  2: { intros a H%in_map_iff. destruct H as (n & <- & H). apply hNat_size_bound. }
  rewrite map_length. lia. 
Qed. 

Definition c__hflatBound := (c__hNatSize + 5) * (c__concat + 1) + c__hflat + 1 + (c__map + 1). 
Definition poly__hflat n := ((n + 1) * (poly__hNat n + 1) + ((n+1) * (n+1) + n + 1) + 1) * c__hflatBound.
Lemma hflat_time_bound fpr l : hflat_time fpr l <= poly__hflat (size (enc fpr) + size (enc l)).
Proof. 
  unfold hflat_time. rewrite map_time_bound_env. 
  2: { 
    split; [ intros | ]. 
    - rewrite hNat_time_bound. poly_mono hNat_poly. 2: apply Nat.le_add_r with (m := size (enc ele)). reflexivity. 
    - apply hNat_poly. 
    } 
  poly_mono hNat_poly. 
  2: (replace_le (size (enc (Sigma fpr))) with (size (enc fpr)) by (rewrite FlatPR_enc_size; lia)); reflexivity.

  rewrite concat_time_bound. poly_mono concat_poly. 
  2: { 
    rewrite map_hNat_size_bound. rewrite list_size_length. 
    replace_le (Sigma fpr) with (size (enc fpr)) by (rewrite size_nat_enc_r with (n := Sigma fpr); rewrite FlatPR_enc_size; lia). 
    reflexivity. 
  } 
  unfold poly__concat. 
  rewrite list_size_length.
  unfold poly__hflat, c__hflatBound. unfold c__hNatSize, c__concat, c__hflat, c__map. nia. 
Qed. 
Lemma hflat_poly : monotonic poly__hflat /\ inOPoly poly__hflat.    
Proof. 
  split; unfold poly__hflat; smpl_inO; apply hNat_poly. 
Qed. 

Lemma hflat_length fpr l : |hflat fpr l| = (Sigma fpr) * |l|. 
Proof. 
  induction l; cbn; [lia | ]. 
  rewrite app_length, hNat_length. unfold hflat, canonicalHom in IHl. rewrite IHl. 
  nia.
Qed. 

Lemma hflat_size_bound fpr l : size (enc (hflat fpr l)) <= 9 * (|l|) * (Sigma fpr) + 4. 
Proof. 
  rewrite list_size_of_el by (intros; apply size_bool).
  rewrite hflat_length. nia.
Qed. 

(*hwindow *)
Definition c__hwindow := 9. 
Definition hwindow_time (fpr : FlatPR) (win : PRWin nat) := hflat_time fpr (prem win) + hflat_time fpr (conc win) + c__hwindow. 
Instance term_hwindow : computableTime' hwindow (fun fpr _ => (1, fun win _ => (hwindow_time fpr win, tt))). 
Proof. 
  extract. solverec. unfold hwindow_time, c__hwindow. solverec. 
Defined. 

Definition poly__hwindow n := poly__hflat n + poly__hflat n + c__hwindow. 
Lemma hwindow_time_bound fpr win : hwindow_time fpr win <= poly__hwindow (size (enc fpr) + size (enc win)).
Proof. 
  unfold hwindow_time. rewrite !hflat_time_bound. 
  unfold poly__hwindow. 
  poly_mono hflat_poly. 2: { replace_le (size (enc (prem win))) with (size (enc win)) by (rewrite PRWin_enc_size; lia). reflexivity. }
  poly_mono hflat_poly at 2. 2: { replace_le (size (enc (conc win))) with (size (enc win)) by (rewrite PRWin_enc_size; lia). reflexivity. }
  lia. 
Qed. 
Lemma hwindow_poly : monotonic poly__hwindow /\ inOPoly poly__hwindow. 
Proof. 
  unfold poly__hwindow; split; smpl_inO; apply hflat_poly. 
Qed. 

(*Lemma hwindow_size_bound fpr l : size (enc (hflat*)

(*hwindows *)
Definition c__hwindows := c__windows + 3. 
Definition hwindows_time (fpr : FlatPR) := map_time (fun w => hwindow_time fpr w) (windows fpr) + c__hwindows.
Instance term_hwindows : computableTime' hwindows (fun fpr _ => (hwindows_time fpr, tt)). 
Proof. 
  extract. solverec. unfold hwindows_time, c__hwindows. solverec. 
Defined. 

Definition c__hwindowsBound := (c__hwindows + 1) * (c__map + 1).
Definition poly__hwindows n :=  ((n + 1) * (poly__hwindow (n+ n) + 1) + 1) * c__hwindowsBound.
Lemma hwindows_time_bound fpr : hwindows_time fpr <= poly__hwindows (size (enc fpr)). 
Proof. 
  unfold hwindows_time. 
  rewrite map_time_bound_env. 2: split; [ intros; apply hwindow_time_bound | apply hwindow_poly]. 
  rewrite list_size_length. 
  replace_le (size (enc (windows fpr))) with (size (enc fpr)) by (rewrite FlatPR_enc_size; lia) at 1. 
  poly_mono hwindow_poly. 
  2: { replace_le (size (enc (windows fpr))) with (size (enc fpr)) by (rewrite FlatPR_enc_size; lia) at 1. reflexivity. }
  unfold poly__hwindows, c__hwindowsBound. nia.
Qed. 
Lemma hwindows_poly : monotonic poly__hwindows /\ inOPoly poly__hwindows. 
Proof. 
  unfold poly__hwindows; split; smpl_inO. 
  - apply hwindow_poly. 
  - eapply inOPoly_comp; [apply hwindow_poly | apply hwindow_poly | smpl_inO].
Qed. 

(*hfinal *)
Definition c__hfinal := c__final + 3. 
Definition hfinal_time (fpr : FlatPR) := map_time (fun l => hflat_time fpr l) (final fpr) + c__hfinal. 
Instance term_hfinal : computableTime' hfinal (fun fpr _ => (hfinal_time fpr, tt)). 
Proof. 
  extract. solverec. unfold hfinal_time, c__hfinal; solverec. 
Defined.

Definition c__hfinalBound := (c__hfinal + 1) * (c__map + 1).
Definition poly__hfinal n :=  ((n + 1) * (poly__hflat (n+ n) + 1) + 1) * c__hfinalBound.
Lemma hfinal_time_bound fpr : hfinal_time fpr <= poly__hfinal (size (enc fpr)). 
Proof. 
  unfold hfinal_time. 
  rewrite map_time_bound_env. 2: split; [ intros; apply hflat_time_bound | apply hflat_poly]. 
  rewrite list_size_length. 
  replace_le (size (enc (final fpr))) with (size (enc fpr)) by (rewrite FlatPR_enc_size; lia) at 1. 
  poly_mono hflat_poly. 
  2: { replace_le (size (enc (final fpr))) with (size (enc fpr)) by (rewrite FlatPR_enc_size; lia) at 1. reflexivity. }
  unfold poly__hfinal, c__hfinalBound. nia.
Qed. 
Lemma hfinal_poly : monotonic poly__hfinal /\ inOPoly poly__hfinal. 
Proof. 
  unfold poly__hfinal; split; smpl_inO. 
  - apply hflat_poly. 
  - eapply inOPoly_comp; [apply hflat_poly | apply hflat_poly | smpl_inO].
Qed. 

(*hBinaryPR *)
Definition c__hBinaryPR := 2 * c__Sigma + c__offset + c__width + c__init + c__windows + c__steps + 28.
Definition c__hBinaryPR2 := 38.
Definition hBinaryPR_time (fpr : FlatPR) := c__hBinaryPR2 * (Sigma fpr * offset fpr + Sigma fpr * width fpr + Sigma fpr + hflat_time fpr (init fpr) + hwindows_time fpr + hfinal_time fpr) + c__hBinaryPR.
Instance term_hBinaryPR : computableTime' hBinaryPR (fun fpr _ => (hBinaryPR_time fpr, tt)).
Proof. 
  unfold hBinaryPR. unfold hoffset, hwidth, hsteps, hinit.  
  extract. solverec. 
  unfold hBinaryPR_time, c__hBinaryPR, c__hBinaryPR2. solverec. 
Defined. 

Definition poly__hBinaryPR n := c__hBinaryPR2 * (2 * n * n + n + poly__hflat (n +n) + poly__hwindows n + poly__hfinal n) + c__hBinaryPR. 
Lemma hBinaryPR_time_bound fpr : hBinaryPR_time fpr <= poly__hBinaryPR (size (enc fpr)). 
Proof. 
  unfold hBinaryPR_time. 
  replace_le (Sigma fpr) with (size (enc fpr)) by (rewrite size_nat_enc_r, FlatPR_enc_size; lia). 
  replace_le (offset fpr) with (size (enc fpr)) by (rewrite size_nat_enc_r, FlatPR_enc_size; lia).
  replace_le (width fpr) with (size (enc fpr)) by (rewrite size_nat_enc_r, FlatPR_enc_size; lia).
  rewrite hflat_time_bound. 
  poly_mono hflat_poly. 
  2: { (replace_le (size (enc (init fpr))) with (size (enc fpr)) by (rewrite FlatPR_enc_size; lia)); reflexivity. }
  rewrite hfinal_time_bound. rewrite hwindows_time_bound. 
  unfold poly__hBinaryPR. nia. 
Qed. 
Lemma hBinaryPR_poly : monotonic poly__hBinaryPR /\ inOPoly poly__hBinaryPR. 
Proof. 
  split; unfold poly__hBinaryPR; smpl_inO. all: try solve [apply hflat_poly  | apply hwindows_poly | apply hfinal_poly ].
  eapply inOPoly_comp; [apply hflat_poly | apply hflat_poly | smpl_inO].
Qed. 

(*reduction *)
Definition c__reduction := 9. 
Definition reduction_time (fpr : FlatPR) := FlatPR_wf_dec_time fpr + isValidFlattening_dec_time fpr + hBinaryPR_time fpr + c__reduction.
Local Instance term_reduction : computableTime' reduction (fun fpr _ => (reduction_time fpr, tt)).
Proof. 
  extract. solverec. all: unfold reduction_time, c__reduction; solverec. 
Defined.  

Definition poly__reduction n := poly__FlatPRWfDec n + poly__isValidFlatteningDec n + poly__hBinaryPR n + c__reduction. 
Lemma reduction_time_bound fpr : reduction_time fpr <= poly__reduction (size (enc fpr)). 
Proof. 
  unfold reduction_time, poly__reduction. 
  rewrite FlatPR_wf_dec_time_bound, isValidFlattening_dec_time_bound, hBinaryPR_time_bound. lia. 
Qed. 
Lemma reduction_poly : monotonic poly__reduction /\ inOPoly poly__reduction. 
Proof. 
  split; unfold poly__reduction; smpl_inO. 
  all: try solve [ apply FlatPR_wf_dec_poly | apply isValidFlatteningDec_poly | apply hBinaryPR_poly]. 
Qed. 

(*size bound *)
Lemma reduction_size_bound fpr : exists f, size (enc (reduction fpr)) <= f (size (enc fpr)) /\ inOPoly f /\ monotonic f.
Proof. 
  evar (f : nat -> nat). exists f. split; [ | split]. 
  + unfold reduction. destruct andb. 
    - unfold hBinaryPR. rewrite BinaryPR_enc_size; cbn. 
      rewrite !size_nat_enc. 

Lemma FlatPR_to_BinaryPR_poly : reducesPolyMO (unrestrictedP FlatPRLang) (unrestrictedP BinaryPRLang).
Proof. 
  exists reduction.
  - exists poly__reduction. 
    + constructor. 
      extract.  solverec. 
      all: specialize (reduction_time_bound x) as H1; unfold reduction_time, c__reduction in H1; nia.
    + apply reduction_poly.
    + apply reduction_poly. 
    + evar (f : nat -> nat). exists f. split; [ | split]. 
      * intros fpr. unfold reduction. 


  


