```
(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)
```

# Kruskal-Fan
The Fan theorem for inductive bars and a constructive variant of König's lemma

```coq
Theorem FAN_theorem X (P : rel₁ (list X)) :
      monotone P
    → bar P []
    → bar (λ lw, Forall2 (λ x l, x ∈ l) ∙ lw ⊆₁ P) [].
```

```coq
Theorem af_konig X (R : rel₂ X) (P : nat → rel₁ X) :
      af R
    → (∀ n : nat, fin (P n))
    → ∃ₜ m, ∀v : vec X m, (∀i, P (idx2nat i) v⦃i⦄) → ∃ i j, idx2nat i < idx2nat j ∧ R v⦃i⦄ v⦃j⦄
```
