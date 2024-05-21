(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq
  Require Import List Utf8.

From KruskalTrees
  Require Import tactics list_utils.

From KruskalFinite
  Require Import finite.

Require Import base.

Import ListNotations.

Set Implicit Arguments.

#[local] Hint Resolve Forall2_app in_eq in_cons : core.

#[local] Notation monotone P := (∀ x l, P l → P (x::l)).
#[local] Notation FAN lw := (λ c, Forall2 (λ x l, x ∈ l) c lw).

Section FAN_theorem.

  (** That proof of the FAN theorem on inductive bars is derived
      by significantly reworked from Daniel Fridlender's paper

      https://www.brics.dk/RS/98/39/BRICS-RS-98-39.pdf

      which was designed with ACL2.

      In particular, we completely avoid using an explicit
      computation of the FAN like "list_fan" above
      and instead work directly with the FAN predicate. *)

  Variables (X : Type) (P : rel₁ (list X)) (HP : monotone P).

  Local Fact P_monotone_app l m : P m → P (l++m).
  Proof. induction l; simpl; auto. Qed.

  (* P right-lifted by u holds over all choices seqs of lw 
     Notice that when u is [], we simply get FAN lw ⊆₁ P *)
  Let Plift_on_FAN u lw := FAN lw ⊆₁ λ v, P (v++u).

  Local Fact Plift_on_FAN_monotone u : monotone (Plift_on_FAN u).
  Proof.
    intros ? ? Hv ? (? & ? & ? & ?%Hv & ->)%Forall2_cons_inv_r.
    now apply HP.
  Qed.

  Hint Resolve P_monotone_app Plift_on_FAN_monotone : core.

  Local Lemma bar_P_bar_Plift_on_FAN {u} : bar P u → bar (Plift_on_FAN u) [].
  Proof.
    induction 1 as [ | u _ IHu ].
    + constructor 1; unfold Plift_on_FAN; simpl; auto.
    + constructor 2; intros w.
      induction w as [ | a w IHw ].
      * constructor 1.
        (* FAN [[]] is empty *)
        intros _ (_ & _ & [] & _)%Forall2_cons_inv_r.
      * (* We combine IHu and IHv using bar_intersection *)
        specialize (IHu a).
        apply bar_app_nil in IHw.
        apply bar_app_nil.
        generalize (@Plift_on_FAN_monotone (a::u)); intros Hu.
        assert (monotone (λ v, Plift_on_FAN u (v++[w]))) as Hw by (simpl; auto).
        generalize (bar_intersection Hu Hw IHu IHw).
        clear Hu Hw IHu IHw; unfold Plift_on_FAN.
        (* The result follows by mono(tonicity) *)
        apply bar_mono.
        intros ? [] ? (? & ? & ? & [<- | ] & ->)%Forall2_snoc_inv_r; eauto.
        rewrite <- app_assoc; auto.
  Qed.

  (* The FAN theorem for list based FANs
     If a (monotone) P is unavoidable starting from []
     then P is also uniformly unavoidable on FANs starting from [] *)
  Theorem FAN_theorem : bar P [] → bar (λ lw, FAN lw ⊆₁ P) [].
  Proof.
    (* Plift_on_FAN [] is equivalent to λ lw, FAN lw ⊆₁ P *)
    intros H.
    apply bar_mono with (2 := bar_P_bar_Plift_on_FAN H).
    intros ? H1 ? ?%H1; now rewrite <- app_nil_r.
  Qed.

End FAN_theorem.
