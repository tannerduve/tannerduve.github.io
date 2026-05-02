---
layout: post
title: "Currying in Categories"
date: 2026-04-30 13:00:00 -0800
description: Cartesian closed categories and the Curry-Howard correspondence
categories: Formal-Verification
tags: functional-programming category-theory
tikzjax: true
thumbnail: assets/img/MelliesClassicalComputationalTrilogy.jpg
---

> The central dogma of computational trinitarianism holds that Logic, Languages, and Categories are but three manifestations of one divine notion of computation.
>
> — Robert Harper

## Introduction

I was recently having a conversation with a mathematician about functional programming and Curry-Howard, and of course I had to bring up the less-talked-about third pillar of the correspondence, i.e. the language of cartesian closed categories. So I wanted to write a post introducing this idea.

Functional programmers are all familiar with the idea of "currying", i.e. that a function of two arguments can be thought of as a function of one argument which returns another function of one argument. The same idea generalizes to any arity. 

An immediate use of this is partial application; say I have an addition function on naturals, `add : ℕ → ℕ → ℕ`. I can write `add 3` and I get a function `ℕ → ℕ` which adds 3 to its input. 

This allows for combinator-style point-free (pointless?) programming with higher-order combinators like `map`, `fold`, `(.)`, or what have you, since each multi-argument function is just a one-argument function which can apply more functions. 

We will see that currying is an elegant and natural notion, in the sense that it falls cleanly out of the mathematical ground underlying functional programming.

## The Curry-Howard correspondence

The Curry-Howard correspondence is a deep connection between functional programming and formal logic. In essence, you can read a proof of $A \implies B$ as a *function* which transforms evidence of $A$ into evidence of $B$, and conversely you can read a function of type `A → B` as a proof of $A \implies B$. 

That is, we can read *propositions* as *types*, and *proofs* as *programs* (I implore everyone to read Wadler's [Propositions as Types](https://homepages.inf.ed.ac.uk/wadler/papers/propositions-as-types/propositions-as-types.pdf), or at least watch his [talk](https://www.youtube.com/watch?v=IOiZatlZtGU&time_continue=1&source_ve_path=NzY3NTg&embeds_referring_euri=https%3A%2F%2Fwww.google.com%2F)). 

This extends to the other connectives in basic logic: "and" corresponds to the cartesian product of types, "or" to their disjoint sum, "true" to the unit type, and "false" to the void/empty type. 

This can be made formal; taking a look at the proof rules for intuitionistic logic and the typing rules for the simply typed lambda calculus, up to some notational differences, we are really looking at the same thing:

<div class="row">
    <div class="col-sm mt-3 mt-md-0">
        {% include figure.liquid path="assets/img/intuitionistic-proof-rules.png" title="Intuitionistic proof rules" class="img-fluid rounded z-depth-1" %}
    </div>
    <div class="col-sm mt-3 mt-md-0">
        {% include figure.liquid path="assets/img/stlc-typing-rules.png" title="STLC typing rules" class="img-fluid rounded z-depth-1" %}
    </div>
</div>
<div class="caption">
    Left: natural deduction rules for intuitionistic logic with conjunction and implication. Right: typing rules for the simply typed lambda calculus with products. Reproduced from Abramsky & Tzevelekos (see references).
</div>

This correspondence is what we call Curry-Howard, and it underlies modern proof assistants. Propositions are types, proofs are programs, and they all live together in languages like Lean and Coq.

## Lambek's contribution: the third pillar

Joachim Lambek introduced a third member to this connection by providing a model of the simply typed lambda calculus in a *cartesian closed category*, which we will define in a moment.

He showed that programs in a simply typed lambda calculus (equivalently, proofs in intuitionistic logic) can be interpreted as morphisms in a cartesian closed category, and that this interpretation is sound and complete: if two lambda terms are $\beta\eta$-equivalent, they are interpreted as the same morphism (soundness), and vice versa (completeness). 

What we now have is the following: propositions are types are objects, and proofs are programs are morphisms. This extends to higher-order type systems, such as dependent types, and really several other logics and type systems (see [Propositions as Sessions](https://www.pst.ifi.lmu.de/~petersen/lehre/ss17/sessiontypes/wadler-propositions-as-sessions.pdf) for a Curry-Howard view of linear logic).

## Cartesian closed categories

Now let's define what cartesian closed categories are. 

First consider the [categorical product](https://en.wikipedia.org/wiki/Product_(category_theory)) construction. When a category $\mathbf{C}$ has binary products, this means for any objects $A, B$ in $\mathbf{C}$, there is a *product* $A \times B$ defined by a certain universal property.

We can view this as a functor: denote by $- \times B : \mathbf{C} \to \mathbf{C}$ the functor which sends an object $A$ to $A \times B$. We say a category is *cartesian closed* if the following hold:

1. It has a terminal object.
2. It has binary products.
3. For any object $B$, the product functor $- \times B$ has a *right adjoint*.

The right adjoint to the product functor is often called the internal-hom or the exponential, and is denoted $(-)^B$. Let's unpack what this means.

## Currying as an adjunction

Recall that two functors $F : \mathbf{C} \to \mathbf{D}$ and $G : \mathbf{D} \to \mathbf{C}$ are *adjoint* (written $F \dashv G$) when for any objects $A \in \mathbf{C}$ and $B \in \mathbf{D}$ we have a natural isomorphism

$$\mathrm{Hom}_{\mathbf{D}}(FA,\, B) \;\cong\; \mathrm{Hom}_{\mathbf{C}}(A,\, GB).$$

Applying this to $(- \times B) \dashv (-)^B$, we get for any object $C$ a bijection on hom-sets natural in $A$ and $C$.

$$\mathrm{Hom}_{\mathbf{C}}(A \times B,\, C) \;\cong\; \mathrm{Hom}_{\mathbf{C}}(A,\, C^B)$$

This object $C^B$ in a category of types is exactly the function type $B \to C$. 

This third axiom of cartesian closed categories is telling us that functions from $A \times B$ into $C$ are equivalent to functions from $A$ into the function type $B \to C$, which is *exactly* what currying says. Currying falls out of the definition of our categorical model.

## Summary of the correspondence

We can summarize the correspondence as follows:

| Intuitionistic Logic | Type Theory | Programming | Category Theory |
|---|---|---|---|
| Proposition $A$ | Type $A$ | Data type declaration | Object $A$ |
| Falsity $\bot$ | Empty type $\emptyset$ | Void type (uninhabited) | Initial object $\mathbf{0}$ |
| Truth $\top$ | Unit type $()$ | Unit type (singleton) | Terminal object $\mathbf{1}$ |
| Proof of $A$ | Term $t : A$ | Program of type $A$ | Morphism $f : 1 \to A$ |
| Assumption $A$ | Variable $x : A$ | Function parameter | Identity morphism $\mathrm{id}_A : A \to A$ |
| Implication $A \to B$ | Function type $A \to B$ | Function declaration | Morphism $f : A \to B$ |
| Conjunction $A \wedge B$ | Product type $A \times B$ | Tuple/record type (e.g., `(A, B)` in Haskell) | Binary product $A \times B$ |
| Disjunction $A \vee B$ | Sum type $A + B$ | Enum/tagged union type (e.g., `Either A B` in Haskell) | Binary coproduct $A + B$ |
| Universal quantification $\forall x.\, P(x)$ | Dependent product $\Pi x : A.\, B(x)$ | Dependent function (e.g., `(x : A) → B x` in Lean) | Right adjoint to pullback $\Pi_f \dashv f^*$ |
| Existential quantification $\exists x.\, P(x)$ | Dependent sum $\Sigma x : A.\, B(x)$ | Existential type (e.g., `⟨a, b⟩ : Σ x : A, B x` in Lean) | Left adjoint to pullback $f^* \dashv \Sigma_f$ |
| Negation $\neg A$ | Function $A \to \bot$ | Function to `Void` | Exponential $\mathbf{0}^A$ |

## Generalizing further: closed monoidal categories

We've seen currying in functional programming, and we've now seen where currying comes from in the categorical semantics. This can be generalized further, not just to cartesian closed categories, but to any *closed monoidal category*. A closed monoidal category is exactly a category with a monoidal product and an internal hom, such that the two structures are compatible in the above way.

As an example, if you've ever taken a linear algebra class (a cool linear algebra class, at least), you may have seen the tensor-hom adjunction, stating that linear maps from the tensor product $A \otimes B$ into $C$ are in bijection with linear maps from $A$ into the space of linear maps $\mathrm{Hom}(B, C)$:

$$\mathrm{Hom}(A \otimes B,\, C) \;\cong\; \mathrm{Hom}(A,\, \mathrm{Hom}(B, C))$$

As you can see, this is essentially the same as the statement above. The category of modules over a commutative ring is indeed closed monoidal, and this theorem holds for any closed monoidal category. This is the general setting currying comes from.

## References

- Philip Wadler, [_Propositions as Types_](https://homepages.inf.ed.ac.uk/wadler/papers/propositions-as-types/propositions-as-types.pdf).

- Samson Abramsky and Nikos Tzevelekos, [_Introduction to Categories and Categorical Logic_](https://arxiv.org/abs/1102.1313), Springer-Verlag, 2011.

- Joachim Lambek and Philip J. Scott, _Introduction to Higher Order Categorical Logic_, Cambridge University Press, 1986.