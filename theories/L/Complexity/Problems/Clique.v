From Undecidability.L Require Import L.
From Undecidability.L.Tactics Require Import LTactics ComputableTactics.
From Undecidability.L.Datatypes Require Import LProd LTerm LNat Lists LOptions.
From Undecidability.L.Complexity Require Import NP Synthetic Monotonic LinTimeDecodable Tactics Problems.LGraph.
From Undecidability.L.Functions Require Import Size.


(* k-Clique: duplicate-free list of k nodes such that all pairwise-distinct nodes are connected *)
Inductive isLClique (g : Lgraph) : list Lnode -> nat -> Prop :=
| isLCliqueB : isLClique g [] 0
| isLCliqueS (cl : list Lnode) (node : Lnode) (k : nat) : isLClique g cl k ->
    (not (node el cl)) -> Lgraph_node_in_dec g node = true -> (forall (node' : Lnode), node' el cl -> Lgraph_edge_in_dec g node node' = true) -> isLClique g (node :: cl) (S k).                                                     

Lemma isLClique_node_in (g : Lgraph) (k : nat) (cl : list Lnode) : isLClique g cl k -> forall n, n el cl -> Lgraph_node_in_dec g n = true. 
Proof.
  induction 1. 
  -intros n [].
  - intros n [-> | H3]. apply H1. now apply IHisLClique. 
Qed. 

Lemma isLClique_length (g : Lgraph) (k : nat) (cl : list Lnode) : isLClique g cl k -> k = (|cl|).
Proof. induction 1; now cbn. Qed. 

Definition isLClique_explicit (g : Lgraph) (cl : list Lnode) (k : nat) :=
  |cl| = k /\ dupfree cl /\ (forall n, n el cl -> Lgraph_node_in_dec g n = true) /\ (forall (n m : nat), n <> m -> n el cl -> m el cl -> Lgraph_edge_in_dec g n m = true).
Lemma isLClique_explicit_correct (g : Lgraph) (cl : list Lnode) (k : nat) :
  isLClique g cl k <-> isLClique_explicit g cl k. 
Proof.
  split.
  - induction 1.
    + split; try split. constructor. split. intros n []. intros _ n m _ []. 
    + destruct IHisLClique as [IH1 [IH2 [IH3 IH4]]]. split; try split. now rewrite <- IH1.  
      now constructor. split.
      -- intros n [-> | H3]. apply H1. now apply IH3. 
      -- intros n m H5 [-> | F1] [-> | F2].  
         * congruence.
         * now apply H2. 
         * destruct g as (nodes & e).
           destruct (Lgraph_edge_in_dec_correct (nodes, e) m n) as [H6 _].
           specialize (H6 (H2 n F1)). apply (Lgraph_edge_in_dec_correct (nodes, e) n m). tauto. 
         * now apply IH4.  
  - revert k. induction cl.
    * intros k H. destruct H as [H1 [H2 [H3 H4]]]. cbn in H1; rewrite <- H1. constructor.
    * intros [] [H1 [H2 [H3 H4]]]. 
      -- cbn in H1. congruence. 
      -- constructor. apply IHcl. split. cbn in H1. lia. 
         split. now inv H2.
         split. intros m H. now apply H3. 
         intros m1 m2 F1 F2 F3. now apply H4.
         now inv H2. now apply H3. 
         intros m H. apply H4. inv H2. now intros ->. now left. now right. 
Qed. 

(** *TODO: include well-formedness*)
Definition LClique (input : Lgraph * nat) :=
  let (g, k) := input in exists cl, @isLClique g cl k. 

Definition LClique_verifier (input : Lgraph * nat) (cert : list Lnode) :=
  let (g, k) := input in isLClique g cert k. (*this includes that l is short enough*)

Lemma size_nat_enc_mono (n  :nat) (m : nat) :
  n <= m -> size (enc n) <= size(enc m). 
Proof. 
  intros H; repeat rewrite size_nat_enc. lia. 
Qed. 

Fixpoint connectedb (g : Lgraph) (cl : list Lnode) :=
  match cl with [] => true
           | (n :: cl) => forallb (Lgraph_edge_in_dec g n) cl && connectedb g cl
  end. 

(*TODO: maybe factor out the 2nd induction*)
Lemma connectedb_correct (g : Lgraph) (cl : list Lnode) : dupfree cl -> connectedb g cl = true <-> forall u v, u <> v -> u el cl -> v el cl -> Lgraph_edge_in_dec g u v = true. 
Proof. 
  intros F0. 
  destruct g. induction cl. 
  + cbn. tauto. 
  + split; cbn.
  - intros H%andb_prop; destruct H as [F1 F2]. intros u v neq [H1 | H1] [H2 | H2].
    * congruence.
    * rewrite H1 in *; clear H1.
      apply (proj1 (forallb_forall (Lgraph_edge_in_dec (n, l) u) cl) F1 v H2 ).
    * rewrite H2 in *; clear H2.
      specialize (proj1 (forallb_forall (Lgraph_edge_in_dec (n, l) v) cl) F1 u H1) as H0.
      apply (Lgraph_edge_in_dec_correct (n, l)). apply (Lgraph_edge_in_dec_correct (n, l)) in H0. tauto.
    * inv F0. apply IHcl; tauto. 
  - intros H. apply utils.andb_and; split.
    2: {apply IHcl. firstorder. now inv F0. firstorder. }
    clear IHcl. induction cl. reflexivity. 
    cbn. apply utils.andb_and; split.
    2: {inv F0. inv H3. assert (dupfree (a :: cl)). constructor. firstorder. apply H5. apply IHcl;firstorder. }
    apply H. inv F0. 1-2: firstorder. right; left; reflexivity. 
Qed. 

Definition LClique_verifierb (g : Lgraph) (k : nat) (cl : list Lnode) :=
  forallb (Lgraph_node_in_dec g) cl && dupfreeb Nat.eqb cl && connectedb g cl && Nat.eqb (|cl|) k.   

Definition nat_eqb_correct := (fun a b => conj (proj2 (Nat.eqb_eq a b)) (proj1 (Nat.eqb_eq a b))). 

Lemma LClique_verifierb_correct (g : Lgraph) (k : nat) (cl : list Lnode) :
  reflect (isLClique g cl k) (LClique_verifierb g k cl). 
Proof.
  destruct LClique_verifierb eqn:H; constructor; rewrite isLClique_explicit_correct. 
  - split; try split; try split; unfold LClique_verifierb in H; simp_bool.
    3: now rewrite forallb_forall in H0.
    now apply nat_eqb_correct. 
    all: rewrite <- (reflect_iff (dupfree cl) (dupfreeb Nat.eqb cl) (dupfreeb_correct nat_eqb_correct cl)) in H3.
    assumption. now rewrite connectedb_correct in H2. 
  - intros [H1 [H2 [H3 H4]]]. unfold LClique_verifierb in H. simp_bool.
    + now rewrite <- forallb_forall in H3. 
    + now rewrite -> (reflect_iff (dupfree cl) (dupfreeb Nat.eqb cl) (dupfreeb_correct nat_eqb_correct cl)) in H2.
    + now rewrite <- connectedb_correct in H4. 
    + now apply nat_eqb_correct in H1. 
Qed. 

From Undecidability.L.Complexity Require Import PolyBounds ONotation Monotonic. 

(*extraction of needed functions and derivation of runtime bounds in terms of encoding size*)

Fixpoint connectedb_time (g : Lgraph) (cl : list Lnode) :=
  let (n, e) := g in 
  match cl with [] => 4
              | (cl :: cls) => forallb_time
  (fun (v : Lnode) (_ : unit) =>
  (list_in_decb_time pair_eqb_nat_time e (cl, v) +
    list_in_decb_time pair_eqb_nat_time e (v, cl) + 26, tt)) cls + 19 + connectedb_time g cls
            end. 

Instance term_connectedb : computableTime' connectedb (fun g _ => (5, fun cl _ => (connectedb_time g cl, tt))).
Proof.
  extract. 
  solverec. 
Qed. 

Lemma connectedb_time_bound : exists (f : nat -> nat), (forall (g : Lgraph) (cl : list Lnode), connectedb_time g cl <= f (size(enc g) + size(enc cl))) /\ inOPoly f /\ monotonic f.
Proof.
  (*bound the running time of each step*)
  (*the step function used with forall is not closed, therefore the running time function needs to explicitly capture the needed *)
  (*environment variables *)
  pose (forallb_step_time := fun (env : Lgraph * Lnode) => let (g, a) := env in (fun (v : nat) (_ : unit) => (Lgraph_edge_in_dec_time g a v, tt))).
  pose (step_time := fun (g : Lgraph) cl cls => forallb_time (forallb_step_time (g, cl)) cls + 19).

  (*We would like to get a polynomial in g and the clique cl*)
  assert (exists (f : nat -> nat), (forall (g : Lgraph) (cl : list Lnode) (a : Lnode) (cls: list Lnode),
             a el cl -> subsequence cls cl -> step_time g a cls <= f(size(enc g) + size(enc cl)))
             /\ inOPoly f /\ monotonic f) as (f' & H1 & H2 & H3).
  {
    destruct (Lgraph_edge_in_dec_time_bound) as (f__edgeIn & F1 & F2 & F3).
    (*In order to instantiate forallb_time_bound_env, we need to prove another result first*)
    assert (exists (f' : nat -> nat), (forall a env, fst (forallb_step_time env a tt) <= f'(size (enc a) + size(enc env))) /\ inOPoly f' /\ monotonic f').
    {
      exists f__edgeIn. split.
      - intros node (e & node'). unfold forallb_step_time. cbn. rewrite F1. setoid_rewrite size_prod at 2; cbn[fst snd].
        unfold monotonic in F3; apply F3. lia. 
      - tauto. 
    }
    destruct (forallb_time_bound_env H) as (f__forall & E1 & E2 & E3).
    evar (f : nat -> nat). exists f. split.
    - intros. unfold step_time. rewrite E1. rewrite size_prod; cbn [fst snd]. 
      unfold monotonic in E3. rewrite E3 with (x' := size(enc g) + 2 * size (enc cl)  + 4). 
      instantiate (f := fun n => f__forall (2 * n + 4) + 19). subst f. cbn. 
      rewrite <- Nat.add_le_mono_r. apply E3. lia. 
      rewrite (list_subsequence_size_bound H1). 
      rewrite (list_el_size_bound H0). lia. 
    - subst f; split; smpl_inO. apply inOPoly_comp; smpl_inO. 
  }

  evar (f : nat -> nat). exists f. split.
  - intros g cl. unfold connectedb_time.
    instantiate (f:= fun n => 4 + f' n * n). subst f.
    destruct g as (n, e). induction cl.
    + lia.
    + rewrite IHcl. specialize (H1 (n, e) (a::cl) a cl).
      unfold step_time, forallb_step_time, Lgraph_edge_in_dec_time in H1. rewrite H1.
      3: exists [a], []; firstorder.  2: now left.
      rewrite list_size_cons at 3.
      unfold monotonic in H3.
      rewrite H3 with (x:= size(enc(n, e)) + size(enc(cl)))(x' := size(enc(n, e)) + size(enc(a::cl))).
      solverec.
      rewrite (list_size_cons); lia. 
  - subst f; split; smpl_inO. 
Qed. 

Definition Lclique_verifierb_time (g : Lgraph) (k:nat) (cl : list Lnode):= forallb_time (fun n _ => (33 + 14 * n, tt)) cl
  + dupfreeb_time (fun x _ => (5, fun y _ => (min x y * 17 + 9, tt))) cl
  + connectedb_time g cl + 11 * (|cl|) + 17 * min (|cl|) k + 53.

Instance term_LClique_verifierb : computableTime' LClique_verifierb (fun g _ => (1, fun k _ => (1, fun cl _ => (Lclique_verifierb_time g k cl, tt)))). 
Proof.
  extract. 
  solverec. unfold Lclique_verifierb_time. solverec. 
Qed. 

Lemma Lclique_verifierb_time_bound : exists (f : nat -> nat) , (forall (g: Lgraph) (k : nat) (cl : list Lnode), Lclique_verifierb_time g k cl <= f(size(enc g) + size(enc cl))) /\ inOPoly f /\ monotonic f. 
Proof.
  assert (exists (f : nat -> nat), (forall (a : Lnode), fst((fun n _ => (33 + 14 * n, tt)) a tt) <= f(size(enc a))) /\ inOPoly f /\ monotonic f).
  {
    evar (f : nat -> nat); exists f; split.
    - intros a. cbn -[Nat.mul Nat.add]. rewrite size_nat_enc. 
      instantiate (f := fun n => 4 * n + 17); subst f; lia. 
    - split; subst f; smpl_inO. 
  }
  destruct (forallb_time_bound H) as (f__forall & H1 & H2 & H3); clear H.

  assert (exists (f : nat -> nat), (forall (a b : nat), callTime2 (fun x _ => (5, fun y _ => (min x y * 17 + 9, tt))) a b <= f(size(enc a) + size(enc b))) /\ inOPoly f /\ monotonic f).
  {
    evar (f : nat -> nat). exists f; split.
    - intros a b. cbn -[Nat.add]. rewrite Nat.le_min_r. solverec.
      instantiate (f := fun n => 17 * n + 14). subst f. 
      specialize size_nat_enc_r with (n:= b). lia.
    - split; subst f; smpl_inO.
  }
  destruct (dupfreeb_time_bound H) as (f__dupfree & F1 & F2 & F3); clear H.

  destruct (connectedb_time_bound) as (f__connected & E1 & E2 & E3).

  evar (f : nat -> nat). exists f. split.
  - intros g k cl. unfold Lclique_verifierb_time. 
    rewrite H1, F1, E1. rewrite Nat.le_min_l. repeat rewrite list_size_length.
    unfold monotonic in H3, F3.
    rewrite H3 with (x':= size(enc g) + size(enc cl)) by lia.
    rewrite F3 with (x':= size(enc g) + size(enc cl)) by lia. 
    instantiate (f := fun n => f__connected n + f__forall n + f__dupfree n + 28 * n + 53); subst f.
    solverec.
  - subst f; split; smpl_inO.
Qed.

Lemma clique_inNP : inNP LClique. 
Proof.
  apply (inNP_intro) with (R:= LClique_verifier).
  1: { apply linDec_polyTimeComputable. }
  3 : {
    intros [g k]; split.
    - destruct g. intros (cert & H1). exists cert. easy.  
    - intros (cert & H). now exists cert. 
  }
  2 : {
    evar (f' : nat -> nat). 
    exists f'. split. 2: split. 
    2: {
      intros [g k] cert H. cbn in H.
      assert (k = (|cert|)) by (now apply isLClique_length with (g:= g)).
      rewrite H0 in *; clear H0 k. rewrite size_prod; cbn [fst snd].
      rewrite size_nat_enc. rewrite size_list.
      (*LHS is in O(max_node * |cert|) *)
      specialize (isLClique_node_in H) as H2. 
      unfold Lgraph_node_in_dec in H2. destruct g.
      assert (sumn (map (fun (x : nat ) => size (enc x) + 5) cert) <= (size(enc n) + 5) * (|cert|)).
      - induction cert. cbn; lia.
        cbn. assert (a <= n).
        { assert (Lgraph_node_in_dec (n, l) a = true ).
          apply isLClique_node_in with (k:= |a::cert|) (cl:= a::cert); easy.
          cbn in H0. destruct n. congruence. dec_bool. lia.
        }
        apply size_nat_enc_mono in H0. rewrite H0. rewrite IHcert. solverec.
        now inv H. firstorder. 
      - rewrite H0. rewrite size_prod with (w := (n, l)); cbn [fst snd].
        instantiate (f' := fun n => 4 * n * n). subst f'.
        solverec.
    }
    all: (subst f'; smpl_inO).
  }

  destruct (Lclique_verifierb_time_bound) as (f' & H1 & H2 & H3).
  evar (f : nat -> nat). exists f. split; try split.
  - exists (fun inp => match inp with ((g, k), cert) => LClique_verifierb g k cert end).
    split.
    + constructor. extract. solverec.
      repeat (rewrite size_prod; cbn [fst snd]).
      rewrite H1. rewrite size_prod; cbn [fst snd].
      instantiate (f:= fun n => f'(n) + 11). subst f.
      cbn. unfold monotonic in H3. rewrite H3 at 1.
      2 : {
        assert (size(enc a) + size(enc b1) + 4 + size(enc b) <= size(enc a) + size(enc b1) + 4 + size(enc b0) + 4+ size(enc b) + 4).
        2: apply H. lia.
      }
      reflexivity. 
  + intros [[g k] b]. specialize (LClique_verifierb_correct g k) as H4.
    destruct (reflect_iff (isLClique g b k) (LClique_verifierb g k b)) as (F1 & F2). apply H4.
    split; cbn; tauto. 
 - subst f; smpl_inO. 
 - subst f; smpl_inO. 
Qed. 