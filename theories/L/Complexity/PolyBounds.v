
From Undecidability.L.Complexity Require Export NP ONotation. 
From Undecidability.L.Tactics Require Import LTactics.
From Undecidability.L.Complexity Require Import MorePrelim.
From Undecidability.L Require Export Datatypes.LLists Datatypes.LLNat.
From Undecidability.L.Functions Require Import EqBool. 

(** why the heck isn't this in the standard library? no one knows... *)
Instance proper_lt_mul : Proper (lt ==> eq ==> le) Nat.mul. 
Proof. 
  intros a b c d e f. nia.
Qed. 

Instance proper_lt_add : Proper (lt ==> eq ==> le) Nat.add.
Proof. 
  intros a b c d e f. nia. 
Qed. 

Instance proper_le_pow : Proper (le ==> eq ==> le) Nat.pow.
Proof. 
  intros a b H1 d e ->. apply Nat.pow_le_mono_l, H1. 
Qed. 

Instance mult_lt_le : Proper (eq ==> lt ==> le) mult. 
Proof. 
  intros a b -> d e H. nia. 
Qed.

Instance add_lt_lt : Proper (eq ==> lt ==> lt) Nat.add. 
Proof. 
  intros a b -> c d H. lia.
Qed.

Instance le_lt_impl : Proper (le --> eq ==> Basics.impl) lt. 
Proof. 
  intros a b H d e ->. unfold Basics.flip in H. unfold Basics.impl. lia. 
Qed.

Instance lt_le_impl : Proper (lt --> eq ==> Basics.impl) le. 
Proof. 
  intros a b H d e ->. unfold Basics.flip in H. unfold Basics.impl. lia.  
Qed.

Lemma list_el_size_bound {X : Type} `{registered X} (l : list X) (a : X) :
  a el l -> size(enc a) <= size(enc l). 
Proof. 
  intros H1. 
  rewrite size_list. 
  induction l. 
  - destruct H1.
  - cbn. destruct H1. rewrite H0; clear H0. solverec. rewrite IHl. 2: assumption. 
    solverec. 
Qed. 

Lemma list_app_size {X : Type} `{registered X} (l l' : list X) :
  size(enc (l ++ l')) + c__listsizeNil = size(enc l) + size(enc l').
Proof.
  repeat rewrite size_list. 
  rewrite map_app. rewrite sumn_app. lia. 
Qed. 

Lemma list_size_at_least {X : Type} `{registered X} (l : list X) : size(enc l) >= c__listsizeNil. 
Proof. rewrite size_list. lia. Qed.

Lemma list_app_size_l {X : Type} `{registered X} (l l' : list X) :
  size(enc (l ++ l')) >= size (enc l). 
Proof. 
  enough (size(enc (l++l')) + c__listsizeNil >= size(enc l) + c__listsizeNil) by lia. 
  rewrite list_app_size.  specialize list_size_at_least with (l:= l'). lia. 
Qed. 

Lemma list_app_size_r {X : Type} `{registered X} (l l' : list X) :
  size(enc (l ++ l')) >= size (enc l'). 
Proof. 
  enough (size(enc (l++l')) + c__listsizeNil >= size(enc l') + c__listsizeNil) by lia. 
  rewrite list_app_size.  specialize list_size_at_least with (l:= l). lia. 
Qed. 

Lemma list_subsequence_size_bound {X : Type} `{registered X} (l l': list X) :
  subsequence l l' -> size (enc l) <= size (enc l').
Proof. 
  intros (C & D & ->). 
  enough (size(enc l) <= size(enc (l++D))). 
  {
    rewrite H0. specialize list_app_size_r with (l:= C) (l' := l++D). lia. 
  }
  specialize list_app_size_l with (l:= l) (l':=D). lia. 
Qed. 

Lemma list_size_cons {X : Type} `{registered X} (l : list X) (a : X) : size(enc (a::l)) = size(enc a) + size(enc l) + c__listsizeCons.
Proof. repeat rewrite size_list. cbn.  lia. Qed. 

Lemma list_size_app (X : Type) (l1 l2 : list X) `{registered X} : size (enc (l1 ++ l2)) <= size (enc l1) + size (enc l2). 
Proof. 
  rewrite <- list_app_size. lia. 
Qed. 

Lemma list_size_concat (X : Type) (l : list (list X)) `{registered X} : size (enc (concat l)) <= size (enc l). 
Proof. 
  induction l; cbn; [easy | ]. 
  now rewrite list_size_app, list_size_cons, IHl. 
Qed. 

Lemma list_size_length {X : Type} `{registered X} (l : list X) : |l| <= size(enc l). 
Proof. 
  rewrite size_list. induction l.
  - cbn; lia. 
  - cbn. rewrite IHl. unfold c__listsizeCons; lia. 
Qed. 

Lemma list_size_enc_length {X : Type} `{registered X} (l : list X) : size (enc (|l|)) <= size (enc l). 
Proof. 
  rewrite size_list. rewrite size_nat_enc. unfold c__natsizeS, c__natsizeO, c__listsizeNil, c__listsizeCons. induction l; cbn; lia. 
Qed. 

Lemma list_size_of_el {X : Type} `{registered X} (l : list X) (k : nat) : (forall a, a el l -> size(enc a) <= k) -> size(enc l) <= (k * (|l|)) + c__listsizeCons * (|l|) +  c__listsizeNil . 
Proof.
  intros H1. induction l. 
  - cbn. rewrite size_list. cbn.  lia.
  - cbn -[c__listsizeCons]. rewrite list_size_cons. rewrite IHl; [ |now firstorder]. rewrite H1; [|now left].
    solverec. 
Qed. 

Lemma map_time_mono (X : Type) (f1 f2 : X -> nat) (l : list X): (forall x : X, x el l -> f1 x <= f2 x) -> map_time f1 l <= map_time f2 l. 
Proof. 
  intros H. induction l; cbn; [lia | ].
  rewrite IHl, H by easy. lia. 
Qed.

Lemma concat_time_exp (X : Type) (l : list (list X)): concat_time l = sumn (map (fun l' => c__concat * length l') l) + (|l| + 1) * c__concat. 
Proof. 
  induction l; cbn -[Nat.add Nat.mul]. 
  - lia.
  - unfold concat_time in IHl. rewrite IHl. lia. 
Qed. 

Lemma sumn_map_mono (X : Type) (f1 f2 : X -> nat) l : (forall x, x el l -> f1 x <= f2 x) -> sumn (map f1 l) <= sumn (map f2 l).
Proof. 
  intros H. induction l; cbn; [lia | ]. 
  rewrite IHl, H by easy. lia. 
Qed.

Lemma sumn_map_const (X : Type) c (l : list X) : sumn (map (fun _ => c) l) = |l| * c. 
Proof. 
  induction l; cbn; [lia | ]. 
  rewrite IHl. lia. 
Qed.

Lemma nat_size_lt a b: a < b -> size (enc a) < size (enc b). 
Proof. 
  intros H. rewrite !size_nat_enc. unfold c__natsizeS; nia. 
Qed.

Lemma nat_size_le a b: a <= b -> size (enc a) <= size (enc b). 
Proof. 
  intros H. rewrite !size_nat_enc. unfold c__natsizeS; nia. 
Qed.

Tactic Notation "replace_le" constr(s) "with" constr(r) "by" tactic(tac) :=
  let H := fresh in assert (s <= r) as H by tac; rewrite !H; clear H. 
Tactic Notation "replace_le" constr(s) "with" constr(r) "by" tactic(tac) "at" ne_integer_list(occ) := 
  let H := fresh in assert (s <= r) as H by tac; rewrite H at occ; clear H. 
Tactic Notation "replace_le" constr(s) "with" constr(r) :=
  let H := fresh in assert (s <= r) as H; [ | rewrite !H; clear H]. 

Tactic Notation "poly_mono" constr(H) "at" integer(occ) :=
  let He := fresh in specialize H as He; match type of He with
                    | _ /\ monotonic _ => unfold monotonic in He; setoid_rewrite (proj2 He) at occ
                    | monotonic _ /\ _ => unfold monotonic in He; setoid_rewrite (proj1 He) at occ
                    end; clear He. 
Tactic Notation "poly_mono" constr(H) :=
  let He := fresh in specialize H as He; match type of He with
                    | _ /\ monotonic _ => unfold monotonic in He; erewrite (proj2 He)
                    | monotonic _ /\ _ => unfold monotonic in He; erewrite (proj1 He)
                    end; clear He. 


Lemma le_add_l n m : m <= n + m. 
Proof. lia. Qed. 

Definition c__moduloBound :=  c__divmod + c__modulo + c__sub.
Lemma modulo_time_bound x y: 
  modulo_time x y <= (size (enc x) + size (enc y) + 1) * c__moduloBound. 
Proof. 
  unfold modulo_time, divmod_time. rewrite size_nat_enc_r with (n := x) at 1. rewrite size_nat_enc_r with (n := y) at 1.
  unfold c__moduloBound. nia. 
Qed. 

Lemma leb_time_bound_l a b: leb_time a b <= (size(enc a) + 1) * c__leb. 
Proof. 
  unfold leb_time. rewrite Nat.le_min_l. rewrite size_nat_enc_r with (n := a) at 1. lia.
Qed. 

Lemma leb_time_bound_r a b : leb_time a b <= (size(enc b) + 1) * c__leb. 
Proof. 
  unfold leb_time. rewrite Nat.le_min_r. rewrite size_nat_enc_r with (n:= b) at 1. lia. 
Qed. 

Section fixX.
  Context {X : Type}.
  Context {H : registered X}.

  (*Elements of type Y capture the environment of higher-order functions. This allows their argument functions to be non-closed, *)
  (* i.e. their running time depends on some values in their environment *)
  Variable (Y : Type).
  Context {RY : registered Y}.

  Lemma list_in_decb_time_bound_env (eqbT : Y -> (X -> X -> nat)) (f : nat -> nat):
    (forall (a b : X) (y : Y), eqbT y a b <= f(size(enc a) + size(enc b) + size(enc y))) /\ monotonic f 
      -> forall (l : list X) (e : X) (y : Y), list_in_decb_time (eqbT y) l e <= ((|l| + 1) * (f(size(enc l) + size(enc e) + size(enc y)) + c__list_in_decb)).  
  Proof.
    intros [H1 H2]. intros. induction l. 
    - rewrite size_list; cbn. nia.
    - cbn [list_in_decb_time]. rewrite IHl, H1. unfold monotonic in H2. 
      rewrite H2 with (x' := size (enc (a ::l)) + size(enc e) + size(enc y)). 
      2: rewrite list_size_cons; unfold c__list_in_decb; nia. 
      setoid_rewrite H2 with (x' := size (enc (a ::l)) + size(enc e) + size(enc y)) at 2. 
      2: rewrite list_size_cons; unfold c__list_in_decb; nia. 
      cbn. solverec. 
  Qed. 

  Lemma list_incl_decb_time_bound_env (eqbT : Y -> (X -> X -> nat)) (f : nat -> nat) :
    (forall (a b : X) (y : Y), eqbT y a b <= f (size (enc a) + size (enc b) + size (enc y))) /\ monotonic f
    -> forall (a b : list X) (y : Y), list_incl_decb_time (eqbT y) a b <= ((|a|) + 1) * ((|b|) + 1) * (f (size (enc b) + size (enc a) + size (enc y)) + c__list_in_decb) + (|a|+1) * c__list_incl_decb.
  Proof. 
    intros [H1 H2] a b env. induction a. 
    - cbn -[c__list_incl_decb c__list_in_decb]. lia.
    - cbn -[c__list_incl_decb c__list_in_decb]. rewrite list_in_decb_time_bound_env by easy.
      rewrite IHa. 
      unfold monotonic in H2. 
      rewrite H2. 
      2: { replace_le (size (enc a)) with (size (enc (a::a0))) by (rewrite list_size_cons; lia). reflexivity. }
      setoid_rewrite H2 at 2. 
      2: { replace_le (size (enc a0)) with (size (enc (a::a0))) by (rewrite list_size_cons; lia). reflexivity. }
      nia. 
  Qed. 

  Definition c__dupfreeBound := c__dupfreeb + c__list_in_decb. 
  Lemma dupfreeb_time_bound_env (eqbT : Y -> X -> X -> nat) (f : nat -> nat): 
    (forall (a b : X) (y : Y), eqbT y a b <= f (size (enc a) + size (enc b) + size(enc y))) /\ monotonic f 
     -> forall (l : list X) (y : Y), dupfreeb_time (eqbT y) l <= (|l| + 1) * (|l| + 1) * (f (2* size (enc l) + size (enc y)) + c__dupfreeBound). 
  Proof.  
    intros [H1 H2]. intros. induction l.  
    - unfold c__dupfreeBound. cbn -[Nat.add]. lia.  
    - cbn -[c__dupfreeBound c__list_in_decb]. rewrite IHl. rewrite list_in_decb_time_bound_env by easy.   
      rewrite !Nat.add_0_r. 
      unfold monotonic in H2. erewrite H2. 
      2: (replace_le (size (enc l) + size (enc a)) with (size (enc (a::l)) + size(enc(a::l))) by (rewrite list_size_cons; lia)); reflexivity. 
      setoid_rewrite H2 at 2.  
      2: (replace_le (size(enc l)) with (size (enc (a::l))) by (rewrite list_size_cons; lia)); reflexivity. 
      unfold c__dupfreeBound. cbn [Nat.mul]. rewrite !Nat.add_0_r. 
      nia. 
  Qed. 

  Lemma forallb_time_bound_env (predT : Y -> X -> nat) (f : nat -> nat):
    (forall (a : X) (y : Y), predT y a <= f (size(enc a) + size(enc y))) /\ monotonic f 
    -> forall (l : list X) (y : Y), forallb_time (predT y) l <= (|l| +1) * (f(size (enc l) + size(enc y)) + c__forallb). 
  Proof. 
    intros [H1 H2]. intros. induction l. 
    - cbn. lia.   
    - cbn. rewrite IHl, H1. unfold monotonic in H2. 
      rewrite H2 with (x' := size (enc (a :: l)) + size(enc y)). 2: rewrite list_size_cons; nia. 
      setoid_rewrite H2 with (x' := size(enc (a::l)) + size(enc y)) at 2. 2: rewrite list_size_cons; nia. 
      nia.
  Qed. 

  Lemma nth_error_time_bound : 
    forall (l : list X) n, nth_error_time l n <= (min (size (enc l)) (size (enc n)) + 1) * c__ntherror.
  Proof.
    intros. unfold nth_error_time. rewrite size_nat_enc_r with (n := n) at 1. rewrite list_size_length. nia.
  Qed. 

  Lemma map_time_bound_env (fT : Y -> X -> nat) (f__bound : nat -> nat): 
    (forall (env : Y) (ele : X), fT env ele <= f__bound (size (enc env) + size (enc ele))) /\ monotonic f__bound
    -> forall (env : Y) (l : list X), map_time (fT env) l <= (|l| + 1) * (f__bound (size (enc env) + size (enc l)) + 1) * (c__map + 1). 
  Proof. 
    intros [H1 H2] env l. induction l; cbn -[c__map]. 
    - nia. 
    - rewrite IHl. rewrite H1. unfold monotonic in H2. 
      rewrite H2 at 1. 2: (replace_le (size (enc a)) with (size (enc (a::l))) by (rewrite list_size_cons; lia)); reflexivity. 
      setoid_rewrite H2 at 2. 2: (replace_le (size (enc l)) with (size (enc (a::l))) by (rewrite list_size_cons; lia)); reflexivity. 
      nia. 
  Qed. 

  Definition poly__concat n := (n + 1) * c__concat.
  Lemma concat_time_bound (l : list (list X)) : concat_time l <= poly__concat (size (enc l)). 
  Proof. 
    unfold concat_time. induction l; cbn -[Nat.add Nat.mul].
    - unfold poly__concat. nia. 
    - rewrite IHl. unfold poly__concat. rewrite list_size_cons. rewrite list_size_length. unfold c__concat, c__listsizeCons; nia.
  Qed. 
  Lemma concat_poly : monotonic poly__concat /\ inOPoly poly__concat. 
  Proof. 
    split; unfold poly__concat; smpl_inO. 
  Qed. 
End fixX.

Section fixXY.
  Context {X Y Z: Type}.
  Context {H:registered X}.
  Context {H0: registered Y}.
  Context {H1 : registered Z}.

  Lemma fold_right_time_bound_env (step : Z -> Y -> X -> X) (stepT : Z -> Y -> X -> nat) (f__arg f__size : nat -> nat): 
    (forall (acc : X) (ele : Y) (env : Z), stepT env ele acc <= f__arg (size (enc acc) + size (enc ele) + size (enc env))) /\ monotonic f__arg
    -> (forall (acc : X) (ele : Y) (env : Z), size (enc (step env ele acc)) <= size (enc acc) + f__size (size (enc ele) + size (enc env))) /\ monotonic f__size
    -> forall (l : list Y) (acc : X) (env : Z), fold_right_time (step env) (stepT env) l acc <= (|l| + 1) * f__arg (|l| * f__size (size(enc l) + size (enc env)) + size (enc acc) + size(enc l) + size (enc env)) + (|l| + 1) * c__fold_right. 
  Proof. 
    intros [G1 G2] [F1 F2] l init env. 
    (*we first show that the output size of foldr on every suffix is bounded by |l| * fsize(size(enc l) + size(enc env)) + size(enc init) *)
    assert (forall l' l'', l = l' ++ l'' -> size (enc (fold_right (step env) init l'')) <= |l''| * f__size(size (enc l'') + size (enc env)) + size (enc init)) as H3. 
    { 
      intros l' l''. revert l'. induction l''; intros.
      - cbn. lia. 
      - cbn. rewrite F1. rewrite IHl''. 2: { now rewrite app_comm_cons' in H2. } 
        unfold monotonic in F2. setoid_rewrite F2 at 2. 
        2: (replace_le (size(enc a)) with (size (enc (a::l''))) by (apply list_el_size_bound; eauto)); reflexivity. 
        rewrite F2 at 1. 2: (replace_le (size (enc l'')) with (size (enc (a::l''))) by (rewrite list_size_cons; lia)); reflexivity. 
        nia. 
    } 

    induction l. 
    - cbn -[c__fold_right]. lia. 
    - cbn -[c__fold_right]. rewrite IHl. clear IHl.
      2: { intros. specialize (H3 (a::l') l''). apply H3. rewrite H2. eauto. } 
      rewrite G1. 
      unfold monotonic in *. erewrite G2. 
      2: { rewrite H3. 2: assert (a::l = [a] ++l) as -> by eauto; easy.
           erewrite F2. 2: (replace_le (size (enc l)) with (size (enc (a::l))) by (rewrite list_size_cons; lia)); reflexivity. 
           replace_le (size (enc a)) with (size (enc (a::l))) by (rewrite list_size_cons; lia). 
           instantiate (1 := (f__size (size (enc (a :: l)) + size (enc env)) + (| l |) * f__size (size (enc (a :: l)) + size (enc env)) + size (enc init) + size (enc (a :: l)) + size (enc env))). 
           nia. 
        } 
      setoid_rewrite G2 at 2. 
      2: { 
        instantiate (1 := (f__size (size (enc (a :: l)) + size (enc env)) + (| l |) * f__size (size (enc (a :: l)) + size (enc env)) + size (enc init) + size (enc (a :: l)) + size (enc env))).
        rewrite F2. 2: (replace_le (size(enc l)) with (size (enc (a::l))) by (rewrite list_size_cons; lia)); reflexivity. 
        replace_le (size (enc l)) with (size (enc (a::l))) by (rewrite list_size_cons; lia). lia.
      } 
      nia.
  Qed. 
End fixXY.
