From Undecidability.L Require Export L Tactics.Extract.
Require Import PslBase.Bijection String.

(** * Correctness and time bounds *)

(* Typeclass for registering types *)


Class registered (X : Type) := mk_registered
  {
    enc :> encodable X ; (* the encoding function for X *)
    proc_enc : forall x, proc (enc x) ; (* encodings need to be a procedure *)
    inj_enc : injective enc (* encoding is injective *)
  }.

Hint Mode registered + : typeclass_instances. (* treat argument as input and force evar-freeness*)

Arguments enc : simpl never.  (* Never unfold with cbn/simpl *)

(** ** Correctness *)

(* Definition of the valid types for extraction *)

Inductive TT : Type -> Type :=
  TyB t (R : registered t) : TT t
| TyAll t1 (t2: t1 -> Type) (tt1 : TT t1) (tt2 : (forall x : t1, TT (t2 x)))
  : TT (forall x : t1, t2 x)
| TyAllT {T : Type -> Type} (HT : forall X (R__X : registered X), TT (T X)) : TT (forall X, T X).

Existing Class TT.
Existing Instance TyB.
Existing Instance TyAll.
Existing Instance TyAllT.

  
Arguments TyB _ {_}.
Arguments TyAll {_} {_} _ _.

Hint Mode TT + : typeclass_instances. (* treat argument as input and force evar-freeness*)

Notation "! X" := (TyB X) (at level 69).
Notation "X ~> Y" := (TyAll X (fun _ => Y)) (right associativity, at level 70).


Fixpoint computes {A} (tau : TT A) {struct tau}: A -> L.term -> Type :=
  match tau with
    !_ => fun x xInt => (xInt = enc x)
  | @TyAll A B tau1 tau2 =>
    fun f t_f  =>
      proc t_f * forall (a : A) t_a,
        computes tau1 a t_a
        ->  {v : term & (t_f t_a >* v) * computes (tau2 a) (f a) v}
  | @TyAllT T HT =>
    fun x xInt => {xInt' : term & (xInt = lam xInt') * forall (X:Type) R__X, computes (HT X R__X) (x X) xInt'}%type 
  end%type.

Local Definition registered_nonempty : registered (unit).
exists (fun _ => I). all:cbv. eauto. intros [] []. congruence.
Qed.

Lemma computesProc t (ty : TT t) (f : t) fInt:
  computes ty f fInt -> proc fInt.
Proof.
  induction ty in f,fInt|-*.
  -intros ->. unfold enc. now destruct R. 
  -now intros [? _].
  -intros (?&->&?). split. 2:easy. rewrite closed_dcl. econstructor. eapply closed_dcl_x. eapply H with (R__X:=registered_nonempty). easy.
Qed.

(* This is for a user to give an definition *)
Class computable X {ty : TT X} (x : X) : Type :=
  {
    ext : extracted x;
    extCorrect : computes ty x ext;
  }.

Hint Mode computable + - +: typeclass_instances. (* treat argument as input and force evar-freeness*)

Existing Instance ext | 5.

Global Arguments computable {X} {ty} x.
Global Arguments extCorrect {X} ty x {computable} : simpl never.
Global Arguments ext {X} {ty} x {computable} : simpl never.

Typeclasses Opaque ext.

Lemma proc_ext X (ty : TT X) (x : X) ( H : computable x) : proc (ext x).
Proof.
  unfold ext. destruct H. apply (computesProc extCorrect0). 
Qed.


Instance reg_is_ext ty (R : registered ty) (x : ty) : computable x.
Proof.
  exists (enc x). reflexivity.
Defined.


Lemma computesTyB (t:Type) (x:t) `{registered t}: computes (TyB t) x (ext x).
Proof.
  unfold ext. now destruct R.
Qed.

Instance extApp' t1 t2 {tt1:TT t1} {tt2 : forall x, TT (t2 x)} (f: forall (x:t1), t2 x) (x:t1) (Hf : computable f) (Hx : computable x) : computable (f x).
Proof.
  destruct Hf, Hx.
  edestruct extCorrect0 as [? H].
  edestruct H as (?&?&?).
  eassumption.
  now eapply (@Build_computable _ _ _ x0). 
Defined.  

Lemma extApp t1 t2 {tt1:TT t1} {tt2 : forall x, TT (t2 x)} (f: forall (x:t1), t2 x) (x:t1) (Hf : computable f) (Hx : computable x) :
  (ext f) (ext x) >* ext (f x).
Proof.
  unfold ext, extApp'.
  destruct Hf, Hx.
  destruct extCorrect0 as (? & correct0).
  destruct correct0 as (?&?&?). tauto. 
Qed.

Lemma ext_is_enc t1 (R:registered t1) (x: t1) (Hf : computable x) :
  @ext _ _ x Hf = enc x.
Proof.
  now destruct Hf. 
Defined.

Definition computesExp {t} (ty : TT t) (f:t) (s fExt : term) : Type :=
  eval s fExt * computes ty f fExt.

Lemma computesExpStart t1 (tt1 : TT t1) (f : t1) (fExt : term):
  proc fExt ->
  {v :term & computesExp tt1 f fExt v} ->  computes tt1 f fExt.
Proof.
  intros ? (?&?&?). replace fExt with x. tauto. apply unique_normal_forms. eapply e. eapply H. destruct e as [e ?]. now rewrite e. 
Qed.

Lemma computesExpStep t1 t2 (tt1 : TT t1) (tt2 : TT t2) (f : t1 -> t2) (s:term) (fExt : term):
  eval s fExt -> closed s -> 
  (forall (y : t1) (yExt : term), computes tt1 y yExt -> {v : term & computesExp tt2 (f y) (s yExt) v}%type) ->
  computesExp (tt1 ~> tt2) f s fExt.
Proof.
  intros ? ? H. split. assumption. split. split. now rewrite <-H0. now destruct H0.
  intros ? ? exted.
  edestruct H as (v&?&?). eassumption. 
  eexists v. split. rewrite H0 in e. now rewrite e. eauto.
Qed.

Lemma computesTyArr t1 t2 (tt1 : TT t1) (tt2 : TT t2) f fExt :
  proc fExt
  -> (forall (y : t1) (yExt : term),
        computes tt1 y yExt
        -> {v : term & eval (fExt yExt) v * (proc v -> computes tt2 (f y) v)}%type)
  -> computes (tt1 ~> tt2) f fExt.
Proof.
  intros ? H'.
  split;[assumption|].
  intros y yExt yCorrect.
  edestruct H' as (?&(R&?) & H''). eassumption. 
  eexists. split.
  eassumption. 
  eapply H''.
  split. 2:assumption.
  rewrite <- R. apply app_closed. now destruct H. specialize (computesProc yCorrect) as []. easy.
Qed.

(** Extensional equality to extract similar functions without unsopported features (e.g. informative deciders) instead *)

Fixpoint extEq t {tt:TT t} : t -> t -> Prop:=
  match tt with
    TyB _ => eq
  | @TyAll t1 t2 tt1 tt2 => fun f f' => forall (x : t1), extEq (f x) (f' x)
  | @TyAllT T HT => fun f f' => forall X (R__X: registered X), extEq (f X) (f' X)
  end.


Instance extEq_refl t (tt:TT t): Reflexive (extEq (tt:=tt)).
Proof.
  unfold Reflexive.
  induction tt;cbn.
  -reflexivity.
  -intros f x. eauto.
  -intros. eapply H.
Qed.

Lemma computesExt X (tt : TT X) (x x' : X) s:
  extEq x x' -> computes tt x s -> computes tt x' s.
Proof.
  induction tt as [|? ? ? ? IH1 IH2 |T HT IH]in x,x',s |-*;intros eq.  
  -inv eq. tauto.
  -cbn in eq|-*. intros [H1 H2]. split. 1:tauto.
   intros y t exts.
   specialize (H2 y t exts) as (v&R&H2).
   exists v. split. 1:assumption.
   eapply IH2. 2:now eassumption.
   apply eq.
  -cbn. intros (?&->&?). do 2 eexists. split. intros. eapply IH. all:eauto. 
Qed.

Lemma computableExt X (tt : TT X) (x x' : X):
  extEq x x' -> computable x -> computable x'.
  intros ? (s&?). exists s. eauto using computesExt.
Defined.

(** register a datatype via an (injectve) function to another, e.g. vectors as lists *)

Lemma registerAs X Y `{registered X} (f:Y -> X) : injective f -> registered Y.
Proof.
  intros Hf. eexists (fun x => enc (f x)). now destruct H.
  intros ? ? ?. now eapply H, Hf in H0.
Defined.
Arguments registerAs {_ _ _} _ _.

(** Support for extracting registerAs-ed functions *)
(*
Fixpoint changeResType t1 t2 (tt1:TT t1) (tt2 : TT t2) : {t & TT t}:=
  match tt1 with
    TyB _ => existT _ t2 tt2
  | TyAll tt11 tt12 =>
    existT _ _ (TyAll tt11 (fun x => projT2 (changeResType (tt12 x) tt2)))
  end.

Inductive isResTypeOf {t} (R:registered t) : forall {t1}, TT t1 -> Type :=
  isResTypeOfB : isResTypeOf R (TyB t)
| isResTypeOfAll t1 t2 (tt1:TT t1) (tt2: forall x, TT (t2 x)) : (forall x: t1, isResTypeOf R (tt2 x)) -> isResTypeOf R (TyAll tt1 tt2).

Fixpoint insertCast t1 (tt1 : TT t1) X Y (R__X : registered X) (R__Y: registered Y) (cast : X -> Y) (H:isResTypeOf R__X tt1){struct H}:
  t1 -> projT1 (changeResType tt1 (TyB Y)) :=
  match H  with
    isResTypeOfB _ => fun x => cast x
  | @isResTypeOfAll _ _ t1 t2 tt1 tt2 H => fun f x => (insertCast (tt1:=tt2 x) _ cast (H x)) (f x)
  end.

Lemma cast_registeredAs t1 (tt1 : TT t1) X Y (R: registered Y) (cast : X -> Y) (f:t1)
  (Hc : injective cast) (H:isResTypeOf (registerAs cast Hc) tt1):
  computable (ty:=projT2 (changeResType tt1 (TyB Y))) (insertCast R cast H f) ->
  computable f.
Proof.
  intros (s&exts).
  exists s.
  induction H.
  -cbn in exts|-*;unfold enc in *. destruct R. rewrite exts. reflexivity.
  -destruct exts as (?&exts). split. assumption.
   intros x s__x ext__x.
   specialize (exts x s__x ext__x) as (v &?&exts).
   exists v. split. tauto.
   eapply X0. all:eassumption.
Qed.
*)
Opaque computes.
