From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import LNat Lists LProd.
From Undecidability.L.Computability Require Import MuRec.

From Undecidability Require Import TM.TM.
Require Import PslBase.FiniteTypes.FinTypes.

(** ** Extraction of Turing Machine interpreter  *)

(** *** Encoding finite types *)
(* This is not an instance because we only want it for very specific types. *)
Definition registered_finType `{X : finType} : registered X.
Proof.
  eapply (registerAs index).
  intros x y H. now apply injective_index.
Defined.

Definition finType_eqb {X:finType} (x y : X) :=
  Nat.eqb (index x) (index y).

Lemma finType_eqb_reflect (X:finType) (x y:X) : reflect (x = y) (finType_eqb x y).
Proof.
  unfold finType_eqb. destruct (Nat.eqb_spec (index x) (index y));constructor.
  -now apply injective_index.
  -congruence.
Qed.

Section finType_eqb.
  Local Existing Instance registered_finType.

  Global Instance term_index (F:finType): computableTime' (@index F) (fun _ _=> (1, tt)).
  Proof.
    apply cast_computableTime.
  Qed.

  Global Instance term_finType_eqb (X:finType) : computableTime' (finType_eqb (X:=X)) (fun x _ => (1,fun y _ => (17 * Init.Nat.min (index x) (index y) + 17,tt))).
  Proof.
    extract.
    solverec.
  Qed.
End finType_eqb.



Section Lookup.
  Variable X Y : Type.
  Variable eqb : X -> X -> bool.

  Fixpoint lookup (x:X) (A:list (X*Y)) d: Y :=
    match A with
      [] => d
    | (key,Lproc)::A =>
      if eqb x key then Lproc else lookup x A d
    end.

End Lookup.

Section funTable.

  Variable X : finType.
  Variable Y : Type.
  Variable f : X -> Y.

  Definition funTable :=
    map (fun x => (x,f x)) (elem X).

  Variable (eqb : X -> X -> bool).
  Variable (Heqb:forall x y, reflect (x = y) (eqb x y)).

  Lemma lookup_funTable x d:
    lookup eqb x funTable d = f x.
  Proof.
    unfold funTable.
    specialize (elem_spec x).
    generalize (elem X) as l.
    induction l;cbn;intros Hel.
    -tauto.
    -destruct (Heqb x a).
     +congruence.
     +destruct Hel. 1:congruence.
      eauto.
  Qed.
End funTable.

Definition lookupTime {X Y} `{registered X} (eqbT : timeComplexity (X ->X ->bool)) x (l:list (X*Y)):=
  fold_right (fun '(a,b) res => callTime2 eqbT x a + res +19) 4 l.


Global Instance term_lookup X Y `{registered X} `{registered Y}:
  computableTime' (@lookup X Y) (fun eqb T__eqb => (1, fun x _ => (5, fun l _ => (1, fun d _ => (lookupTime T__eqb x l,tt))))).
extract. unfold lookupTime. solverec.
Qed.

Lemma lookupTime_leq {X Y} `{registered X} (eqbT:timeComplexity (X -> X -> bool)) x (l:list (X*Y)) k:
  (forall y, callTime2 eqbT x y <= k)
  -> lookupTime eqbT x l <= length l * (k + 19) + 4.
Proof.
  intros H'.
  induction l as [ | [a b] l].
  -cbn. omega.
  -unfold lookupTime. cbn [fold_right]. fold (lookupTime eqbT x l).
   setoid_rewrite IHl. cbn [length]. rewrite H'.
   ring_simplify. omega.
Qed.

(** *** Encoding vectors *)

Definition vector_enc {X:Type} {intX : registered X} : forall n, encodable (Vector.t X n) :=
  fix vector_enc (n:nat) (v:Vector.t X n) : term := 
  match v with
  | [||] => lam (lam 1)
  | Vector.cons _ a n0 v' => lam (lam (0 (enc a) (enc n0) (vector_enc n0 v')))
  end.

Instance register_vector X `{registered X} n : registered (Vector.t X n).
Proof.
  exists (vector_enc (n:=n)).
  -induction x;cbn;Lproc.
  -hnf. induction x.
   +intros y. pattern y. eapply Vector.case0. easy.
   +intros y . revert h x IHx. pattern n,y. eapply Vector.caseS with (v:=y).
    clear n y.
    intros h n y h0 x IHx [=].
    f_equal. now apply inj_enc. eapply IHx. eassumption.
Defined.

Lemma vector_enc_correct (X : Type) (intX : registered X) (n:nat) (v : Vector.t X n):
  forall (s : term), proc s -> forall t : term, proc t -> ((enc v) s) t >(<=2) match v with
                                                                  | [||] => s
                                                                  | Vector.cons _ x n v => ((t (enc x)) (enc n)) (enc v)
                                                                  end.
Proof.
  extract match.
Qed.

Hint Resolve vector_enc_correct : Lrewrite.
                                       
Instance termT_cons X `{registered X} : computableTime' (@Vector.cons X) (fun a _ => (1,fun n _ => (1,fun A _ => (1,tt)))).
Proof.
  extract constructor. solverec.
Qed.

Instance term_vector_map X Y `{registered X} `{registered Y}:
  computableTime' (@VectorDef.map X Y)
                 (fun f fT => (1,fun n _ => (5,(fun l _ => (Vector.fold_right (fun (x0 : X) (res : nat) => fst (fT x0 tt) + res + 15) l 4,tt))))).
Proof.
  unfold VectorDef.map. extract. solverec.
Qed.

(*
Fixpoint time_map2 {X Y Z} `{registered X} `{registered Y} `{registered Z} (gT : timeComplexity (X->Y->Z)) (l1 :list X) (l2 : list Y) :=
  match l1,l2 with
  | x::l1,y::l2 => callTime2 gT x y + 18 + time_map2 gT l1 l2
  | _,_ => 9
  end. *)


Run TemplateProgram (tmGenEncode "Empty_set_enc" Empty_set).
Hint Resolve Empty_set_enc_correct : Lrewrite.

Instance TT_empty P: TT (forall e : Empty_set, P e).
eapply TyAll. exact _. intros [].
Defined.

Instance term_Empty_set_rect P : computableTime' (Empty_set_rect P) (fun e _ => (0,Empty_set_rect (fun x => _) e)).
eexists I. split. Lproc.
intros [].
Qed.

Definition vector_caseS_const {A : Type} {P : nat -> Type} {n : nat} (v : Vector.t A (S n)) :=
    match
      v as v0 in (Vector.t _ n0)
      return
      (match n0 as x return (Vector.t A x -> Type) with
       | 0 => fun _ : Vector.t A 0 => Empty_set -> ID
       | S n1 => fun v1 : Vector.t A (S n1) => (forall (h : A) (t : Vector.t A n1), P (S n1)) -> P (S n1)
       end v0)
    with
    | [||] => fun devil : Empty_set => Empty_set_rect (fun _ => ID) devil
    | Vector.cons _ h n0 t => fun (H : forall (h0 : A) (t0 : Vector.t A n0), P (S n0)) => H h t
    end.


Instance term_vector_caseS_const {A : Type} {P : nat -> Type} `{registered A} `{forall n, registered (P n)} :
  computableTime' (@vector_caseS_const A P)
                  (fun n _ => (1,fun v _ => (7,(fun f fT => (callTime2 fT (Vector.hd v) (Vector.tl v) + 1,tt))))).
Proof.
  cbn [timeComplexity]. extract. Unshelve. 8:{ cbn beta zeta;Lsimpl. }
  6:{ cbn beta zeta;Lsimpl. } cbn beta zeta.
  
  lazymatch goal with
      | H : Lock _ |- computesTime _ (match ?x with _ => _ end) _ _=>
    let t := type of x in
    let _G := fresh "_G" in
    evar (_G:Prop);only [_G]:(clear - H;clear H;destruct x);
    unlock H;
    let t := type of H in
    unify t _G; clear _G;lock H
  end. dependent destruct x0.
  repeat Intern.cstep. solverec. exact Logic.I.
Qed.
(*
Definition hd_tl_helper {A:Type} n : A -> Vector.t A n ->  := fun a b => a.



Instance term_ht_tl_helper1 {A : Type}`{registered A} :
  computableTime' (@hd_tl_helper A)
                  (fun n _ => (1,fun a _ => (1,fun v _ => (1,tt)))).
Proof.
  extract.
 *)

Instance term_vector_hd {A : Type}`{registered A} :
  computableTime' (@Vector.hd A)
                  (fun n _ => (1,fun v _ => (1,tt))).
Proof.
  eapply computableTimeExt with
      (x:=fun n v => vector_caseS_const v Basics.const).
  {intros ? v. dependent destruct v. easy. }
  Check (_ : TT (forall (_:nat), A)).
  
  Hint Extern 10 (computableTime (@vector_caseS_const _ _) _) => (refine term_vector_caseS_const) : typeclass_instances.
  extract.
                                                                                
  eassert (H':=extT (@vector_caseS_const A (fun _ : nat => A))). 
  Unshelve. 2:exact _.
  3:{ 
    refine term_vector_caseS_const. }
  extract. exact _. }.
  
  cbn [timeComplexity]. extract. Unshelve. 8:{ cbn beta zeta;Lsimpl. }
  6:{ cbn beta zeta;Lsimpl. } cbn beta zeta.
  
  lazymatch goal with
      | H : Lock _ |- computesTime _ (match ?x with _ => _ end) _ _=>
    let t := type of x in
    let _G := fresh "_G" in
    evar (_G:Prop);only [_G]:(clear - H;clear H;destruct x);
    unlock H;
    let t := type of H in
    unify t _G; clear _G;lock H
  end. dependent destruct x0.
  repeat Intern.cstep. solverec. exact Logic.I.
Qed.

Instance term_vector_map2 A B C `{registered A} `{registered B} `{registered C}:
  computableTime' (@VectorDef.map2 A B C)
                 (fun f fT => (1,fun n _ => (5,(fun l _ => (1,(fun l' _ => (cnst 0(*Vector.fold_right (fun (x0 : X) (res : nat) => fst (fT x0 tt) + res + 15) l 4*),tt))))))).
Proof.
  cbn [id].
  eapply computableTimeExt with
      (x:=fix map2 f {n} : VectorDef.t A n -> VectorDef.t B n -> VectorDef.t C n :=
         match n with
           0 => fun _ _ => [||]
         | S n => fun va vb=> let (a,va) := (Vector.hd va,Vector.tl va) in
                          let (b,vb) := (Vector.hd vb,Vector.tl vb) in
                          f a b ::: map2 f va vb
         end).
  2:{
    extract. Unshelve. 6:{ Lsimpl. Guarded.
  Unshelve. Focus 5.
  
  unfold VectorDef.map2. extract. solverec.
Qed.

Instance term_vector_map2 A B C `{registered A} `{registered B} `{registered C}:
  computableTime' (@VectorDef.map2 A B C)
                 (fun f fT => (1,fun n _ => (5,(fun l _ => (1,(fun l' _ => (cnst 0(*Vector.fold_right (fun (x0 : X) (res : nat) => fst (fT x0 tt) + res + 15) l 4*),tt))))))).
Proof.
  cbn [id].
  eapply computableTimeExt with
      (x:=fix map2 f {n} : VectorDef.t A n -> VectorDef.t B n -> VectorDef.t C n :=
         match n with
           0 => fun _ _ => [||]
         | S n => fun va vb=> Vector.caseS'
                            va _ (fun a va => Vector.caseS'
                                             vb (fun _ => VectorDef.t C (S n)) (fun b vb => f a b ::: map2 f va vb))
         end).
  2:{
    extract.
  Unshelve. Focus 5.
  
  unfold VectorDef.map2. extract. solverec.
Qed.

Instance term_map2 n A B C `{registered A} `{registered B} `{registered C} (g:A -> B -> C) gT:
  computableTime' g gT-> computableTime' (Vector.map2 g (n:=n)) (fun l1 _ => (1,fun l2 _ => (time_map2 gT (Vector.to_list l1) (Vector.to_list l2) +8,tt))).
Proof.
  intros ?.
  computable_casted_result.
  pose (f:=(fix f t a : list C:=
              match t,a with
                t1::t,a1::a => g t1 a1 :: f t a
              | _,_ => []
              end)).
  assert (computableTime' f (fun l1 _ => (5,fun l2 _ => (time_map2 gT l1 l2,tt)))).
  {subst f; extract.



   solverec. }
  apply computableTimeExt with (x:= fun t a => f (Vector.to_list t) (Vector.to_list a)).
  2:{extract. solverec. }
  induction n;cbn.
  -do 2 destruct x using Vector.case0. reflexivity.
  -destruct x using Vector.caseS'. destruct x0 using Vector.caseS'.
   cbn. f_equal. apply IHn.
Qed.


Lemma time_map2_leq X Y Z `{registered X}  `{registered Y}  `{registered Z}  (fT:timeComplexity (X -> Y -> Z))(l1 : list X) (l2:list Y) k:
  (forall x y, callTime2 fT x y <= k) ->
  time_map2 fT l1 l2<= length l1 * (k+18) + 9.
Proof.
  intros H';
    induction l1 in l2|-*;cbn [time_map2].
  -intuition.
  -destruct l2;ring_simplify. intuition.
   rewrite H',IHl1. cbn [length]. ring_simplify. intuition.
Qed.*)


Run TemplateProgram (tmGenEncode "move_enc" move).
Hint Resolve move_enc_correct : Lrewrite.

Section fix_sig.
  Variable sig : finType.
  Context `{reg_sig : registered sig}.

  (** *** Encoding Tapes *)
  Section reg_tapes.
    Implicit Type (t : TM.tape sig).

    Run TemplateProgram (tmGenEncode "tape_enc" (TM.tape sig)).
    Hint Resolve tape_enc_correct : Lrewrite.

    (**Internalize constructors **)

    Global Instance term_leftof : computableTime' (@leftof sig) (fun _ _ => (1, fun _ _ => (1,tt))).
    Proof.
      extract constructor.
      solverec.
    Qed.

    Global Instance term_rightof : computableTime' (@rightof sig) (fun _ _ => (1, fun _ _ => (1,tt))).
    Proof.
      extract constructor. solverec.
    Qed.

    Global Instance term_midtape : computableTime' (@midtape sig) (fun _ _ => (1, fun _ _ => (1,fun _ _ => (1,tt)))).
    Proof.
      extract constructor. solverec.
    Qed.

    Global Instance term_tape_move_left' : computableTime' (@tape_move_left' sig) (fun _ _ => (1, fun _ _ => (1,fun _ _ => (12,tt)))).
    Proof.
      extract. solverec.
    Qed.

    Global Instance term_tape_move_left : computableTime' (@tape_move_left sig) (fun _ _ => (23,tt)).
    Proof.
      extract. solverec.
    Qed.

    Global Instance term_tape_move_right' : computableTime' (@tape_move_right' sig) (fun _ _ => (1, fun _ _ => (1,fun _ _ => (12,tt)))).
    Proof.
      extract. solverec.
    Qed.

    Global Instance term_tape_move_right : computableTime' (@tape_move_right sig) (fun _ _ => (23,tt)).
    Proof.
      extract. solverec.
    Qed.

    Global Instance term_tape_move : computableTime' (@tape_move sig) (fun _ _ => (1,fun _ _ => (48,tt))).
    Proof.
      extract. solverec.
    Qed.

    Global Instance term_left : computableTime' (@left sig) (fun _ _ => (10,tt)).
    Proof.
      extract. solverec.
    Qed.

    Global Instance term_right : computableTime' (@right sig) (fun _ _ => (10,tt)).
    Proof.
      extract. solverec.
    Qed.

    Global Instance term_tape_write : computableTime' (@tape_write sig) ((fun _ _ => (1,fun _ _ => (28,tt)))).
    Proof.
      extract. solverec.
    Qed.

  End reg_tapes.

  Definition mconfig_enc {states : finType} {R2 : registered states} {n:nat} : encodable (mconfig sig states n) :=
    fun c => match c return term with
            mk_mconfig a b => lam ((var 0 (enc a)) (enc b))
          end.

  Instance register_mconfig (states : finType) (R2 : registered states) (n:nat) : registered (mconfig sig states n).
  Proof.
    exists mconfig_enc.
    -induction x;cbn;Lproc.
    -intros [] [] [= H1 H2]. eapply inj_enc in H1. apply inj_enc in H2. easy.
  Defined.

  Lemma mconfig_enc_correct (states : finType) (R2 : registered states) (n:nat) (c : mconfig sig states n):
    forall (s : term), proc s -> (enc c) s >(<=1) (match c with mk_mconfig a b => (app s (enc a)) (enc b) end).
  Proof.
    extract match.
  Qed.

  Hint Resolve mconfig_enc_correct : Lrewrite.
  
  Instance term_mk_mconfig (states : finType) (R2 : registered states) (n:nat): computableTime' (@mk_mconfig sig states n)
                                                                                         (fun a _ => (1,fun b _ => (1,tt))).
  Proof.
    extract constructor. solverec.
  Qed.

  Global Instance term_cstate (B : finType) `{registered B} n: computableTime' (@cstate sig B n) (fun _ _ => (5,tt)).
  Proof.
    extract. solverec.
  Qed.

  Global Instance term_ctapes (B : finType) `{registered B} n: computableTime' (@ctapes sig B n) (fun _ _ => (5,tt)).
  Proof.
    extract. solverec.
  Qed.

End fix_sig.

Hint Resolve mconfig_enc_correct : Lrewrite.
Hint Resolve tape_enc_correct : Lrewrite.



(* Fixpoint time_loop f fT p pT := cnst 1. *)

Definition Halt' Sigma n (M: mTM Sigma n) (start: mconfig Sigma (states M) n) :=
  exists (f: mconfig _ (states M) _), halt (cstate f)=true /\ exists k, loopM start k = Some f.

Definition Halt :{ '(Sigma, n) : _ & mTM Sigma n & tapes Sigma n} -> _ :=
  fun '(existT2 _ _ (Sigma, n) M tp) =>
    exists (f: mconfig _ (states M) _), halt (cstate f) = true
                                   /\ exists k, loopM (mk_mconfig (start M) tp) k = Some f.

Fixpoint loopTime {X} `{registered X} f (fT: timeComplexity (X -> X)) (p: X -> bool) (pT : timeComplexity (X -> bool)) (a:X) k :=
  fst (pT a tt) +
  match k with
    0 => 7
  |  S k =>
     fst (fT a tt) + 13 + loopTime f fT p pT (f a) k
  end.

Instance term_loop A `{registered A} :
  computableTime' (@loop A)
                 (fun f fT => (1,fun p pT => (1,fun a _ => (5,fun k _ =>(loopTime f fT p pT a k,tt))))).
Proof.
  extract.
  solverec.
Qed.

Section loopM.
  Context (sig : finType).
  Let reg_sig := @registered_finType sig.
  Existing Instance reg_sig.
  Variable n : nat.
  Variable M : mTM sig n.

  Let reg_states := @registered_finType (states M).
  Existing Instance reg_states.

  Run TemplateProgram (tmGenEncode "False_enc" False).
  Hint Resolve False_enc_correct : Lrewrite.

  Fixpoint vector_eqbTime {X} `{registered X} (eqbT: timeComplexity (X -> X -> bool)) {n m} (A : Vector.t X n) (B:Vector.t X m) :=
    match A,B with
      a:::A,b:::B => callTime2 eqbT a b + 25 + vector_eqbTime eqbT A B
    | _,_ => 10
    end.

 

  Instance term_vector_eqb X `{registered X}:
    computableTime'
      (@VectorEq.eqb X)
      (fun eqb T__eqb => (1,fun m _ => (5, fun n _ => (1,fun A _ => (1,fun B _ => (vector_eqbTime T__eqb A B,tt)))))).
  Proof.
    extract. Unshelve. all:try solve [exact Logic.I|exact True]. solverec.
  Qed.

  Definition vector_eqbTime_leq {X} `{registered X} (eqbT: timeComplexity (X -> X -> bool)) {n' m} (A : Vector.t X n') (B:Vector.t X m) k:
    (forall a b, callTime2 eqbT a b <= k)
    -> vector_eqbTime eqbT A B <= min n' m * (k+25) + 10.
  Proof.
    intros H'. induction A in m,B|-*.
    -cbn. omega.
    -destruct B.
     {cbn. intuition. }
     cbn - [callTime2]. setoid_rewrite IHA.
     rewrite H'. ring_simplify. intuition.
  Qed.
  (*
  Lemma list_eqbTime_bound_r {X} `{registered X} (eqbT: timeComplexity (X -> X -> bool)) {n' m} (A : Vector.t X n') (B:Vector.t X m) f:
    (forall (x y:X), callTime2 eqbT x y <= f y) ->
    vector_eqbTime eqbT A B <= sumn (map f B) + 10 + m * 25.
  Proof.
    intros H'.
    induction A in m,B|-*;unfold list_eqbTime;fold list_eqbTime. cbn. now Lia.lia.
    destruct B.
    -cbn. Lia.lia.
    -cbn [vector_eqbTime sumn map]. rewrite H',IHA. Lia.lia.
  Qed.*)

  

  Definition transTime := (length (elem (states M) )*17 + n * 17 * (length ( elem sig )+ 4) + 71) * length (funTable (trans (m:=M))) + 24.

  (** *** Computability of transition relation *)
  Instance term_trans : computableTime' (trans (m:=M)) (fun _ _ => (transTime,tt)).
  Proof.
    pose (t:= (funTable (trans (m:=M)))).
    apply computableTimeExt with (x:= fun c => lookup (prod_eqb finType_eqb (Vector.eqb (LOptions.option_eqb finType_eqb))) c t (start M,Vector.const (None,N) _)).
    2:{extract.
       cbn [fst snd]. intuition ring_simplify.


       rewrite lookupTime_leq with (k:=(17* length (elem (states M)) + 17 * n * (length (elem sig) + 4) + 52)).
       -unfold transTime.

        repeat match goal with
                 |- context C[length _] =>let G:= context C [length t] in progress change G
               end.
        ring_simplify.  omega.
       -intros y. unfold callTime2.
        cbn [fst snd]. ring_simplify.
        setoid_rewrite index_leq at 1 2. rewrite Nat.min_id.
        rewrite vector_eqbTime_leq with (k:= | elem sig| * 17 + 29).
        +nia.
        +intros [] [];unfold callTime2;cbn [fst snd].
         setoid_rewrite index_leq at 1 2. rewrite Nat.min_id.
         all:nia.
    }
    cbn -[t] ;intro. subst t.  setoid_rewrite lookup_funTable. reflexivity.
    apply prod_eqb_spec. apply finType_eqb_reflect. apply vector_eqb_spec,LOptions.option_eqb_spec,finType_eqb_reflect.
  Qed.

  Instance term_current: computableTime' ((current (sig:=sig))) (fun _ _ => (10,tt)).
  Proof.
    extract.
    solverec.
  Qed.

  Instance term_current_chars: computableTime' (current_chars (sig:=sig) (n:=n))  (fun _ _ => (n * 25 +12,tt)).
  Proof.
    extract.
    solverec.
    clear - x.
    induction x;cbn [Vector.fold_right];try nia.
  Qed. 

  Definition step' (c :  mconfig sig (states M) n) : mconfig sig (states M) n :=
    let (news, actions) := trans (cstate c, current_chars (ctapes c)) in
    mk_mconfig news (doAct_multi (ctapes c) actions).


  Instance term_doAct: computableTime' (doAct (sig:=sig)) (fun _ _ => (1,fun _ _ => (89,tt))).
  Proof.
    extract.
    solverec.
  Qed.

  Instance term_doAct_multi: computableTime' (doAct_multi (n:=n) (sig:=sig)) (fun _ _ => (1,fun _ _ =>(n * 108 + 19,tt))).
  Proof.
    extract.
    solverec.
    rewrite time_map2_leq with (k:=90).
    2:now solverec.
    solverec. now rewrite to_list_length.
  Qed.


  Instance term_step' : computableTime' (step (M:=M)) (fun _ _ => (n* 130+ transTime + 64,tt)).
  Proof.
    extract.
    solverec.
  Qed.

  Definition haltTime := length (funTable (halt (m:=M))) * (length (elem (states M)) * 17 + 37) + 12.

  Instance term_halt : computableTime' (halt (m:=M)) (fun _ _ => (haltTime,tt)).
  Proof.
    pose (t:= (funTable (halt (m:=M)))).
    apply computableTimeExt with (x:= fun c => lookup finType_eqb c t false).
    2:{extract.
       solverec.
       rewrite lookupTime_leq with (k:=17 * (| elem (states M) |) + 18).
       2:{
         intros. cbn [callTime2 fst].
         repeat rewrite index_leq. rewrite Nat.min_id. omega.
       }
       unfold haltTime. subst t.
       ring_simplify. reflexivity.
    }
    cbn;intro. subst t. setoid_rewrite lookup_funTable. reflexivity.
    apply finType_eqb_reflect.
  Qed.

  Instance term_haltConf : computableTime' (haltConf (M:=M)) (fun _ _ => (haltTime+8,tt)).
  Proof.
    extract.
    solverec.
  Qed.

  (** *** Computability of step-ndexed interpreter *)
  Global Instance term_loopM :
    let c1 := (haltTime + n*130 + transTime + 85) in
    let c2 := 15 + haltTime in
    computableTime' (loopM (M:=M)) (fun _ _ => (5,fun k _ => (c1 * k + c2,tt))).
  Proof.
    unfold loopM. (* as loop is already an registered instance, this here is a bit out of the scope. Therefore, we unfold manually here. *)
    extract.
    solverec. 
  Qed.

  Instance term_test cfg :
    computable (fun k => LOptions.isSome (loopM (M := M) cfg k)).
  Proof.
    extract.
  Qed.

  Lemma Halt_red cfg :
    Halt' cfg <-> converges (mu (ext ((fun k => LOptions.isSome (loopM (M := M) cfg k))))).
  Proof.
    split; intros.
    - destruct H as (f & ? & k & ?).
      edestruct (mu_complete).
      + eapply term_test.
      + intros. eexists. rewrite !ext_is_enc. now Lsimpl.
      + Lsimpl. now rewrite H0.
      + exists (ext x). split. eauto. Lproc.
    - destruct H as (v & ? & ?). edestruct mu_sound as (k & ? & ? & _).
      + eapply term_test.
      + intros. eexists. now Lsimpl.
      + eassumption.
      + eauto.
      + subst.
        assert ((ext (fun k : nat => LOptions.isSome (loopM cfg k))) (ext k) ==
                ext (LOptions.isSome (loopM cfg k))) by Lsimpl.
        rewrite H1 in H2. clear H1.
        eapply unique_normal_forms in H2; try Lproc. eapply inj_enc in H2.
        destruct (loopM cfg k) eqn:E.
        * exists m. split. 2: eauto.
          unfold loopM in E. now eapply loop_fulfills in E.
        * inv H2.
  Qed.

End loopM.
