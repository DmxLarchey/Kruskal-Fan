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

This project based on [`Kruskal-Trees`](https://github.com/DmxLarchey/Kruskal-Trees), 
[`Kruskal-Finite`](https://github.com/DmxLarchey/Kruskal-Finite) 
and [`Kruskal-AlmostFull`](https://github.com/DmxLarchey/Kruskal-AlmostFull), implements
two additional results related to monotone inductive bars

The Fan theorem for inductive bars stating that is `P` is a _monotone_ predicate on lists 
(ie `P l → P (x::l)`) and is bound to be reached successive by extensions starting from `[]`
then `P` is bound to be reached uniformly over choice sequences of finitary fans:
```coq
Theorem FAN_theorem X (P : rel₁ (list X)) :
      monotone P
    → bar P []
    → bar (λ lw, Forall2 (λ x l, x ∈ l) ∙ lw ⊆₁ P) [].
```

A constructive variant of König's lemma: if `R` is an almost full relation and `P` is
a sequence of finitary choices, then there is a bound `m` (computable if `af` is `Type`-bounded)
such that any choice vector of length `m` (and hence also above), contains a `R`-good pair:  
```coq
Theorem af_konig X (R : rel₂ X) (P : nat → rel₁ X) :
      af R
    → (∀ n : nat, fin (P n))
    → ∃ₜ m, ∀v : vec X m, (∀i, P (idx2nat i) v⦃i⦄) → ∃ i j, idx2nat i < idx2nat j ∧ R v⦃i⦄ v⦃j⦄
```
