(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq
  Require Import List Arith Lia Utf8.

From KruskalTrees
  Require Import notations tactics list_utils idx vec.

From KruskalFinite
  Require Import finite.

Require Import base fan.

Import ListNotations idx_notations vec_notations.

Set Implicit Arguments.

(* good R on the reverse of a vector gives a good pair in the vector *)

#[local] Fact good_rev_vec_list X (R : rel₂ X) n (v : vec X n) :
       good R (rev (vec_list v)) → ∃ i j, idx2nat i < idx2nat j ∧ R v⦃i⦄ v⦃j⦄.
Proof.
   intros (l & y & k & x & r & H1 & H2)%good_iff_split.
   apply f_equal with (f := @rev _) in H2; revert H2.
   rewrite rev_involutive; repeat (rewrite rev_app_distr; simpl); rewrite !app_ass.
   generalize (rev r) (rev k) (rev l); clear l k r; intros l k r; intros H2.
   destruct vec_list_split_inv with (1 := H2) as (p & H3 & H4).
   rewrite <- app_ass, <- app_ass in H2.
   destruct vec_list_split_inv with (1 := H2) as (q & H5 & H6).
   exists p, q; split; auto.
   + rewrite H4, H6, app_ass, !app_length; simpl; lia.
   + subst; auto.
Qed.

Section pfx.

  Variables (X : Type).
  
  Implicit Types (f : nat → X).

  Local Fixpoint pfx f n :=
    match n with
    | 0   => []
    | S n => f 0 :: pfx (λ n, f (S n)) n
    end.

  Local Fact pfx_rev_eq_pfx f n : pfx_rev f n = rev (pfx f n).
  Proof.
    induction n in f |- *; auto.
    rewrite pfx_rev_S; simpl; f_equal; auto.
  Qed.

End pfx.

#[local] Notation FAN lc := (λ c, Forall2 (λ x l, x ∈ l) c lc).

Section choice_vec_list.

  Variable X : Type.
  
  Implicit Types (P : nat → rel₁ X) (f : nat → list X).

  Local Definition choice_vec P n (v : vec X n) := ∀i, P (idx2nat i) v⦃i⦄.

  Local Fixpoint choice_list P l :=
    match l with
    | []   => True
    | x::l => P 0 x ∧ choice_list (λ n, P (S n)) l
    end.

  Local Fact choice_vec_list P n (v : vec _ n) : choice_vec P v ↔ choice_list P (vec_list v).
  Proof.
    induction v as [ | x n v IHv ] in P |- *; simpl.
    + split; auto.
      intros _ i; idx invert i.
    + rewrite <- IHv; split.
      * intros H; split.
        - apply (H idx_fst).
        - intro; apply (H (idx_nxt _)).
      * intros [ H1 H2 ] i; idx invert i; auto.
  Qed.

  Local Fact choice_list_FAN_pfx P f l :
        (∀ n x, P n x ↔ x ∈ f n)
      → choice_list P l ↔ FAN (pfx f ⌊l⌋) l.
  Proof.
    induction l as [ | x l IHl ] in P, f |- *; intros Hf; simpl.
    + split; auto.
    + rewrite Hf, IHl; eauto.
      2: intros ? ?; apply Hf.
      now rewrite Forall2_cons_inv.
  Qed.

End choice_vec_list.

Section af_konig.

  (** A constructive form of König's lemma based on 
     almost full relations. *)

  Variables (X : Type) (R : rel₂ X) (P : nat → rel₁ X)
            (HR : af R) (HP : ∀n, fin (P n)).

  (* This instance of the FAN theorem for good R *)

  Local Lemma bar_good_FAN : bar (λ lc, FAN lc ⊆₁ good R) [].
  Proof.
    apply FAN_theorem.
    + now constructor 2.
    + apply af_iff_bar_good, HR.
  Qed.

  (* P is the FAN of some function f : nat → list X *)

  Let f n := proj1_sig (HP n).

  Local Fact Hf n x : P n x ↔ x ∈ f n.
  Proof. apply (proj2_sig (HP _)). Qed.

  (* We apply bar recursion *)

  Local Lemma good_uniform_over_FAN : ∃ₜ m, FAN (pfx_rev f m) ⊆₁ good R.
  Proof. apply bar_pfx_rev with (1 := bar_good_FAN). Qed.

  Theorem af_konig : ∃ₜ m, ∀v : vec X m, (∀i, P (idx2nat i) v⦃i⦄) → ∃ i j, idx2nat i < idx2nat j ∧ R v⦃i⦄ v⦃j⦄.
  Proof.
    destruct good_uniform_over_FAN as (m & Hm).
    exists m; intros v Hv.
    apply good_rev_vec_list, Hm.
    apply choice_vec_list, choice_list_FAN_pfx with (1 := Hf) in Hv.
    rewrite pfx_rev_eq_pfx, Forall2_rev.
    now rewrite vec_list_length in Hv.
  Qed.

End af_konig.

Check af_konig.

