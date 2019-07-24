From Undecidability.L Require Import Tactics.LTactics Datatypes.LBool Tactics.GenEncode.

(** ** Encoding of option type *)
(* Section Fix_X. *)
(*   Variable X:Type. *)
(*   Variable intX : registered X. *)

(*   (*Run TemplateProgram (tmGenEncode "option_enc" (@option X)).*) 
Hint Resolve option_enc_correct : Lrewrite.

End Fix_X.*)

  
  Definition option_enc : forall X : Type, registered X -> encodable (option X) := 
  fun (X : Type) (intX : registered X) =>
    fix encode (x : option X) : term :=
    match x with
    | Some x0 => lam (lam (var 1 (lam 0) (enc x0)))
    | None => lam (lam (var 0 (lam 0)))
    end.

  Instance registered_option_enc X `{intX:registered X}: registered (@option X).
  Proof.
    eexists (option_enc intX).
    -intros [];cbn. all:Lproc.
    -intros [] [] [=]. now apply inj_enc in H0. easy.
  Defined.

  Lemma option_enc_correct X `{R__X:registered X} (H : option X) (H0 : term) :
      proc H0 -> forall H1 : term, proc H1 -> ((enc H) H0) H1 >(<=2) match H with
                                                             | Some x => H0 (lam 0) (enc x)
                                                             | None => H1 (lam 0)
                                                             end.
  Proof.
    intros. extract match.
  Qed.

Hint Resolve option_enc_correct : Lrewrite.

(* now we must register the non-constant constructors*)

Global Instance term_Some : computableTime' (@Some) (fun X R__X _ _ => (1,tt)).
Proof.
    extract constructor. solverec. 
Defined.

Global Instance term_None : computableTime' (@None) (fun X R__X => tt).
Proof.
    extract constructor. solverec. 
Defined.

(*
Lemma oenc_correct_some X `{R__X:registered X} (s: option X) (v : term) : lambda v -> enc s == ext (@Some X) v -> exists s', s = Some s' /\ v = enc s'.
Proof.
  intros lam_v H. unfold ext in H;cbn in H. unfold extT in H; cbn in H. redStep in H.
  apply unique_normal_forms in H;[|Lproc..]. destruct s;simpl in H.
  -injection H;eauto.
  -discriminate H.
Qed.
       
*)

   (*
   Lemma none_equiv_some v : proc v -> ~ none == some v.
   Proof.
     intros eq. rewrite some_correct. Lrewrite. apply unique_normal_forms in eq;[discriminate|Lproc..].
     intros H. assert (converges (some v)) by (eexists; split;[rewrite <- H; cbv; now unfold none| auto]). destruct (app_converges H0) as [_ ?]. destruct H1 as [u [H1 lu]]. rewrite H1 in H.
     symmetry in H. eapply eqTrans with (s := (lam (lam (#1 u)))) in H.
     eapply eq_lam in H. inv H. symmetry. unfold some. clear H. old_Lsimpl.
   Qed.
    *)

Hint Resolve option_enc_correct : Lrewrite.

Section option_eqb.

  Variable X : Type.
  Variable eqb : X -> X -> bool.
  Variable spec : forall x y, reflect (x = y) (eqb x y).

  Definition option_eqb (A B : option X) :=
    match A,B with
    | None,None => true
    | Some x, Some y => eqb x y
    | _,_ => false
    end.

  Lemma option_eqb_spec A B : reflect (A = B) (option_eqb A B).
  Proof.
    destruct A, B; try now econstructor. cbn.
    destruct (spec x x0); econstructor; congruence.
  Qed.
End option_eqb.

Section int.

  Variable X:Type.
  Context {HX : registered X}.

  Global Instance term_option_eqb : computableTime' (@option_eqb X)
                                                    (fun eqb eqbT => (1, fun a _ => (1,fun b _ => (match a,b with
                                                                                            Some a, Some b => callTime2 eqbT a b + 10
                                                                                          | _,_ => 8 end,tt)))). cbn.
  Proof.
    extract. Unshelve.
    8:{ solverec.
  Defined.

End int.

Definition isSome {T} (u : option T) := match u with Some _ => true | _ => false end.

Instance term_isSome {T} `{registered T} : computable (@isSome T).
Proof.
  extract.
Qed.
