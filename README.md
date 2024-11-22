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

This project is for Coq `8.14+` and is based on [`Kruskal-Trees`](https://github.com/DmxLarchey/Kruskal-Trees), 
[`Kruskal-Finite`](https://github.com/DmxLarchey/Kruskal-Finite) 
and [`Kruskal-AlmostFull`](https://github.com/DmxLarchey/Kruskal-AlmostFull), and
it implements two additional results related to monotone inductive bars.

## The Fan theorem for inductive bars

It states that if `P` is a _monotone_ predicate on lists 
(ie `P l → P (x::l)`) and is bound to be reached by successive extensions starting from `[]`,
then `P` is bound to be reached uniformly over choice sequences of finitary fans:
```coq
Theorem FAN_theorem X (P : rel₁ (list X)) :
      monotone P
    → bar P []
    → bar (λ lw, Forall2 (λ x l, x ∈ l) ∙ lw ⊆₁ P) [].
```

This Fan theorem can be used to justify [`Quasi-Morphisms`](https://github.com/DmxLarchey/Quasi-Morphisms) as used in the proof 
of [Higman's lemma](https://github.com/DmxLarchey/Kruskal-Higman) and [Veldman's version of Kruskal's tree theorem](https://github.com/DmxLarchey/Kruskal-Veldman). 

It is also the base for the termination of algorithms that explore a search-tree that 
avoid good pairs in the search branches, see below.

## A constructive variant of König's lemma

If `R` is an almost full relation and `P` is a sequence of finitary choices, then there is a 
bound `m` (computable if `af` is `Type`-bounded) such that any choice vector of length `m` 
(and hence also above), contains a `R`-good pair:  
```coq
Theorem af_konig X (R : rel₂ X) (P : nat → rel₁ X) :
      af R
    → (∀ n : nat, fin (P n))
    → ∃ₜ m, ∀v : vec X m, (∀i, P (idx2nat i) v⦃i⦄) → ∃ i j, idx2nat i < idx2nat j ∧ R v⦃i⦄ v⦃j⦄
```

A `Type`-bounded variant of this lemma is used in the [constructive proof of decidability for implicational relevance logic](https://github.com/DmxLarchey/Relevant-decidability/tree/v2.0) and the `Prop`-bounded instance is used to establish the 
termination of the computation of the [Friedman `TREE(n)`](https://github.com/DmxLarchey/Friedman-TREE) fast growing function.
