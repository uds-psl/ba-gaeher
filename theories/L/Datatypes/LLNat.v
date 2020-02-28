From Undecidability.L.Tactics Require Export LTactics GenEncode.
Require Import PslBase.Numbers.

Require Import Nat Undecidability.L.Datatypes.LBool Undecidability.L.Datatypes.LProd.
(** ** Encoding of natural numbers *)

Run TemplateProgram (tmGenEncode "nat_enc" nat).
Hint Resolve nat_enc_correct : Lrewrite.

Instance termT_S : computableTime' S (fun _ _ => (1,tt)).
Proof.
  extract constructor.
  solverec.
Defined.

Instance termT_pred : computableTime' pred (fun _ _ => (5,tt)).
Proof.
  extract.
  solverec.
Defined.

Instance termT_plus' : computableTime' add (fun x xT => (5,(fun y yT => (11*x+4,tt)))).
Proof.
  extract.
  fold add. solverec.
Defined.

Definition c__mult1 := 5.
Definition c__mult := 19.
Definition mult_time x y := x * y * c__mult + c__mult * (x+ 1) .
Instance termT_mult : computableTime' mult (fun x xT => (c__mult1,(fun y yT => (mult_time x y,tt)))).
Proof.
  extract. solverec.
  all: unfold mult_time, c__mult1, c__mult; solverec. 
Defined.

Definition c__sub1 := 5.
Definition c__sub := 14. 
Definition sub_time x y := (min x y + 1) * c__sub.
Instance term_sub : computableTime' Nat.sub (fun n _ => (c__sub1,fun m _ => (sub_time n m ,tt)) ).
Proof.
  extract. solverec.
  all: unfold sub_time, c__sub1, c__sub; solverec. 
Defined.

Definition c__leb := 14.
Definition c__leb2 := 5. 
Definition leb_time (x y : nat) := c__leb * (1 + min x y).
Instance termT_leb : computableTime' leb (fun x xT => (c__leb2,(fun y yT => (leb_time x y,tt)))).
Proof.
  extract.
  solverec. all: unfold leb_time, c__leb, c__leb2; solverec. 
Defined.

Definition c__nat_eqb := 17. 
Definition c__nat_eqb2 := 5. 
Definition nat_eqb_time (x y : nat) := c__nat_eqb * (1 + min x y). 
Instance termT_nat_eqb: computableTime' Nat.eqb (fun x xT => (c__nat_eqb2,(fun y yT => (nat_eqb_time x y,tt)))).
Proof.
  extract.
  solverec. all: unfold nat_eqb_time, c__nat_eqb, c__nat_eqb2; solverec. 
Defined.

Instance termT_nat_min : computableTime' Nat.min (fun x _ => (5, fun y _ => (8 + 15 * min x y, tt))).
Proof. 
  extract. solverec. 
Qed. 

Instance termT_nat_max : computableTime' Nat.max (fun x _ => (5, fun y _ => (8 + 15 * min x y, tt))).
Proof. extract. solverec. Qed. 

Definition c__pow1 := 5.
Definition c__pow2 := 10 + c__mult1.
Fixpoint pow_time x n := match n with 
  | 0 => c__pow2 
  | S n => pow_time x n + mult_time x (x ^n) + c__pow2
end.
Instance termT_pow:
  computableTime' Init.Nat.pow   (fun (x : nat) _ => (c__pow1,fun (n : nat) _ => (pow_time x n, tt))).
Proof.
  extract. fold Nat.pow. solverec. 
  all: unfold pow_time, c__pow1, c__pow2; solverec. 
Defined.

Definition c__divmod := 20.
Definition divmod_time (x: nat) := c__divmod * (1+x).
Instance termT_divmod : 
  computableTime' divmod (fun (x : nat) _ => (5, fun (y : nat) _ => (5, fun (q : nat) _ => (1, fun (u : nat) _ => (divmod_time x, tt))))). 
Proof. 
  extract. solverec. all: unfold divmod_time, c__divmod; solverec. 
Defined. 

Definition c__modulo := 21 + c__sub1. 
Definition modulo_time (x :nat) (y : nat) := divmod_time x + c__sub * y + c__modulo.
Instance termT_modulo : 
  computableTime' Init.Nat.modulo (fun x _ => (1, fun y _ => (modulo_time x y, tt))). 
Proof. 
  extract. solverec. 
  - unfold modulo_time, c__modulo; solverec. 
  - unfold sub_time. rewrite Nat.le_min_l. unfold modulo_time, c__modulo. solverec. 
Defined. 

(* now some more encoding-related properties:*)

Fixpoint nat_unenc (s : term) :=
  match s with
  | lam (lam #1) => Some 0
  | lam (lam (app #0 s)) => match nat_unenc s with Some n => Some (S n) | x=>x end
  | _ => None
  end.

Lemma unenc_correct m : (nat_unenc (nat_enc m)) = Some m.
Proof.
  induction m; simpl; now try rewrite IHm.
Qed.

Lemma unenc_correct2 t n : nat_unenc t = Some n -> nat_enc n = t.
Proof with try solve [Coq.Init.Tactics.easy].
  revert n. eapply (size_induction (f := size) (p := (fun t => forall n, nat_unenc t = Some n -> nat_enc n = t))). clear t. intros t IHt n H.
  destruct t. easy. easy.
  destruct t. easy. easy.
  destruct t. 3:easy.
  -destruct n0. easy. destruct n0. 2:easy. inv H. easy.
  -destruct t1. 2-3:easy. destruct n0. 2:easy. simpl in H. destruct (nat_unenc t2) eqn:A.
   +apply IHt in A;simpl;try omega. destruct n. inv H. simpl. congruence.
   +congruence.
Qed.

Lemma dec_enc t : dec (exists n, t = nat_enc n).
Proof.
  destruct (nat_unenc t) eqn:H.
  - left. exists n. now eapply unenc_correct2 in H.
  - right. intros [n A]. rewrite A in H. rewrite unenc_correct in H. inv H.
Qed.

Definition c__natsizeO := 4.
Definition c__natsizeS := 4.
Lemma size_nat_enc (n:nat) :
  size (enc n) = n * c__natsizeS + c__natsizeO.
Proof.
  unfold c__natsizeS, c__natsizeO. 
  induction n;cbv [enc registered_nat_enc] in *. all:cbn [size nat_enc] in *. all:solverec.
Qed.

Lemma size_nat_enc_r (n:nat) :
  n <= size (enc n).
Proof.
    induction n;cbv [enc registered_nat_enc] in *. all:cbn [size nat_enc] in *. all:solverec.
Qed.



(* This is an example for an function in which the run-time of the fix itself is not constant (in add, the fix on the first argument always returns an function in ~5 steps)*)
(* Instance termT_testId : computableTime' (fix f x := *)
(*                                             match x with *)
(*                                               0 => 0 *)
(*                                             | S x => S (f x) *)
(*                                             end). *)
(* Proof. *)
(*   extract. *)
(*   eexists (fun x xT => (x*9+7,tt)). *)
(*   abstract (repeat (cbn;intros;intuition;try destruct _;try ring_simplify)). *)
(* Defined. *)