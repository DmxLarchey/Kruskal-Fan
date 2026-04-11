(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib
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

#[local] Fact list_length_split {X} (m : list X) a b :
    length m = a+b
  → { l : _ 
  & { r | m = l++r
        ∧ length l = a
        ∧ length r = b } }.
Proof.
  intros E.
  exists (firstn a m), (skipn a m); split.
  + now rewrite firstn_skipn.
  + rewrite firstn_length_le, length_skipn; lia.
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

#[local] Abbreviation FAN lc := (λ c, Forall2 (λ x l, x ∈ l) c lc).

Section choice_vec_list.

  Variable X : Type.
  
  Implicit Types (P : nat → rel₁ X) (f : nat → list X).

  Local Definition choice_vec P n (v : vec X n) := ∀i, P (idx2nat i) v⦃i⦄.

  Fixpoint choice_list P l :=
    match l with
    | []   => True
    | x::l => P 0 x ∧ choice_list (λ n, P (S n)) l
    end.

  Fact choice_list_mono P Q : P ⊆₂ Q → choice_list P ⊆₁ choice_list Q.
  Proof.
    intros H l; revert P Q H.
    induction l as [ | x l IHl ]; intros P Q H; simpl; auto.
    intros (? & HP); split; auto.
    revert HP; apply IHl; auto.
  Qed.

  Fact choice_list_app P l m :
      choice_list P (l++m)
    ↔ choice_list P l
    ∧ choice_list (λ n, P (length l+n)) m.
  Proof.
    induction l as [ | ? ? IHl ] in P |- *; simpl; try easy.
    rewrite IHl; tauto.
  Qed.

  Fact choice_list_snoc P l x :
     choice_list P (l++[x])
   ↔ choice_list P l
   ∧ P ⌊l⌋ x.
  Proof.
    rewrite choice_list_app; simpl.
    rewrite Nat.add_0_r; tauto.
  Qed.

  Fact choice_vec_list P n (v : vec _ n) : choice_vec P v ↔ choice_list P (vec_list v).
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

  Fact choice_list_FAN_pfx P f l :
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

  (* P is the FAN of some function α : nat → list X *)

  Local Definition alpha n := proj1_sig (HP n).
  Abbreviation α := alpha.

  (* α n : list X is the support of P n *)
  Local Fact alpha_spec n x : P n x ↔ x ∈ α n.
  Proof. apply (proj2_sig (HP n)). Qed.

  (* Choice lists for P are FANs for [α 0; ... ;α _]
       and hence, (reverse) FANs for [α _; ... ;α 0] *)
  Local Fact choice_list_iff_FAN_alpha l :
    choice_list P l ↔ FAN (pfx_rev α ⌊l⌋) (rev l).
  Proof.
    rewrite pfx_rev_eq_pfx, Forall2_rev.
    apply choice_list_FAN_pfx, alpha_spec.
  Qed.

  (* We apply bar for sequences 
     and get a uniform bound m 
     st FAN [α (n-1); ... ;α 0] ⊆ good R *)
  Local Lemma good_uniform_over_FAN : ∃ₜ m, FAN (pfx_rev α m) ⊆₁ good R.
  Proof. apply bar_pfx_rev with (1 := bar_good_FAN). Qed.

  (* Another way to state the same result *)
  Local Lemma good_uniform_over_FAN_alt : ∃ₜ m, ∀l, choice_list P l → ⌊l⌋ = m → good R (rev l).
  Proof.
    destruct good_uniform_over_FAN as (m & Hm); exists m.
    intro; rewrite choice_list_iff_FAN_alpha.
    intros; apply Hm; now subst.
  Qed.

  Theorem af_konig : ∃ₜ m, ∀v : vec X m, (∀i, P (idx2nat i) v⦃i⦄) → ∃ i j, idx2nat i < idx2nat j ∧ R v⦃i⦄ v⦃j⦄.
  Proof.
    destruct good_uniform_over_FAN as (m & Hm).
    exists m; intros v Hv.
    apply good_rev_vec_list, Hm.
    apply choice_vec_list, choice_list_FAN_pfx with (1 := alpha_spec) in Hv.
    rewrite pfx_rev_eq_pfx, Forall2_rev.
    now rewrite vec_list_length in Hv.
  Qed.

  (** An alternate statement using lists instead of vectors, 
      coming from

           "Constructive substitutes for König lemma", DLW 2025 *)
  Theorem af_konig_choice_list : ∃ₜ m, ∀l, choice_list P l → ⌊l⌋ < m ∨ good R (rev l).
  Proof.
    destruct good_uniform_over_FAN_alt as (m & Hm).
    exists m; intros l H1.
    destruct (le_lt_dec m (length l)) as [ H | ]; auto; right.
    destruct (list_length_split l m (length l-m)) as (l1 & l2 & -> & E & _); try lia.
    apply choice_list_app in H1 as (H1 & _).
    rewrite rev_app_distr.
    apply good_app_left; eauto.
  Qed.

End af_konig.


