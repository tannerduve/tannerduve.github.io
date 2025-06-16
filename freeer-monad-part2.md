---
title: "Part 2: Catamorphisms, Interpreters, and Universal Proprties"
layout: single
permalink: /blog/freeer-monad/part2/
---

In the [last section](/blog/freeer-monad/part1/), we introduced the free monad and implemented it in Lean. In this section we will look into the theory a bit more deeply, by understanding the notions of algebra and universality.

##  1. <a name='Introduction'></a>Introduction: Two Universal Properties

In this part, we will explore two related but distinct universal constructions, both of which will give rise to unique morphisms that, as programmers, we can think of as "interpreters" in different senses. We will be looking at
- **Catamorphisms** from initial algeberas, and
- **Universal morphisms** from free objects

We'll first examine how free monads act as initial algebras, giving us catamorphisms into other algebras. Then, we'll revisit the notion of a free object from part 1, and explain how the free monad induces a universal morphism into any monad equipped with an effect handler. Both of these yield interpreters: catamorphisms interpret by folding data, while universal morphisms interpret by replaying abstract operations in a concrete monad.

<!-- vscode-markdown-toc -->
## Table of Contents

1. [Introduction](#Introduction)
2. [Initial Algebras and Inductive Types](#InitialAlgebras)
    - [Algebras and their Morphisms](#Algebras)
    - [Lists as Initial Algebras](#InductiveTypes)
3. [Free Monads as Initial Algebras](#FreeMonads)
4. [Interpreters as Catamorphisms](#Cata)
5. [The Universal Morphism](#UniversalMorphisms)
6. [Interpreters as Universal Morphisms](#Universal)

<!-- vscode-markdown-toc-config
	numbering=true
	autoSave=true
	/vscode-markdown-toc-config -->
<!-- /vscode-markdown-toc -->

##  1. <a name='InitialAlgebras'></a>Initial Algebras and Inductive Types

Algebra is about manipulating formal expressions. Consider algebraic expressions like $2(x + y)$ or $ax^2 + bx + c$. Notice that there are infinitely many of them, yet only a finite number of rules for making them. This suggests that the rules are used recursively. Let's examine this connection between algebra and recursion a bit, from the perspective of category theory.

**Algebras and their morphisms**  
Let $F : C \to D$ be a functor. An *algebra* over $F$ is a pair $(A, \alpha)$ where $\alpha : FA \to A$.

Given $F$-algebras $(A, \alpha)$ and $(B, \beta)$, $\phi : A \to B$ is an $F$-algebra morphism iff the following diagram commutes:
<div style="text-align: center;">
  <script type="text/tikz">
    \begin{tikzcd}
    	FA && A \\
    	\\
    	FB && B
    	\arrow["\alpha", from=1-1, to=1-3]
    	\arrow["Ff"', from=1-1, to=3-1]
    	\arrow["f", from=1-3, to=3-3]
    	\arrow["\beta"', from=3-1, to=3-3]
    \end{tikzcd}
  </script>
</div>

$F$-algebras and their morphisms form a category, and the initial object in this category is called the *initial algebra*. That is, $(A, \alpha)$ is an initial $F$-algebra iff for any $F$-algebra $(B, \beta)$, there is a unique morphism $\phi : (A, \alpha) \to (B, \beta)$

**Inductive Types**
As it turns out, in terms of categorical semantics, an inductive type is a type whose interpretation is given by an initial algebra of an endofunctor. This was mentioned and shown in part 1 using the example of the `List` type but perhaps was not explained sufficiently. Let's unpack it a bit. First, recall the definition of the type `List α` for an arbitrary type `α`:

```lean
inductive List (α : Type u) where
  | nil : List α
  | cons (head : α) (tail : List α) : List α
```

This says, a list of `α`'s is either empty, OR it consists of a single `α` AND a list of `α`'s. Another way of looking at this type is, as a function which gives you a `List α` given either a `nil` or a `(head : α)` and a `(tail : List α)`.

If you think of "or" as a sum, "and" as a product, and "empty" as a unit, we can express this function as a morphism: 
$$
\phi: \mathbf{1} + (\alpha \times \texttt{List} \alpha) \to \texttt{List} \alpha
$$
That is, $(\texttt{List} \alpha, \phi)$ an *algebra* of the functor:
$$
F_\alpha x = \mathbf{1} + (\alpha \times x)
$$

The next step would be to show that this is initial, ie. that there is a unique morphism from `List α` to any other algebra over $F_\alpha$. Instead of proving this mathematically, let's just write the function in code! As it turns out, this function is already very familiar to anyone that has touched functional programming.

Recall our functor

$$
F_\alpha X = \mathbf{1} + (\alpha \times X)
$$

An $F_\alpha$-algebra is a pair $(B, \beta)$ where $\beta : \mathbf{1} + (\alpha \times B) \to B$. That is, $\beta$ tells you how to collapse either:

- A **unit**, or
- A **pair** `(fst : α, snd : B)`

into a single value of type `B`.

Suppose you want to turn a list into a single value of type `B`. To do that, you need to answer two questions:

1. What should an empty list mean? That is, what value of `B` should `nil` become?

2. What should a cons cell mean? That is, given a head of type `α` and a recursive result of type `B`, how do we combine them into a new `B`?

These two pieces of data:

- A base case `b₀ : B`
- A step function `step : α → B → B`

together define a function:

```lean
β : Unit + (α × B) → B
```

which is exactly the shape of an algebra over $F_\alpha$.

So any such `(B, b₀, step)` forms an $F_\alpha$-algebra.

### The Unique Morphism from `List α`

Now the magic: because `List α` is the *initial algebra* of \$F\_\alpha\$, there exists a **unique morphism** from `List α` to any other \$F\_\alpha\$-algebra `(B, β)`.

This morphism is defined by recursion:

- It sends `nil` to `b₀`
- It sends `cons x xs` to `step x (⟦xs⟧)`, where `⟦xs⟧` is the interpretation of the tail

Let’s define it in Lean:

```lean
def reduce {α β : Type} (b₀ : β) (step : α → β → β) : List α → β
  | [] => b₀
  | x :: xs => step x (reduce b₀ step xs)
```

This may look familiar to you if you have ever used a functional language before, in fact, this is just the `foldr` function! If you've ever written any functional programs you have likely used this plenty.

```lean
def foldr {α β : Type} (b₀ : β) (step : α → β → β) : List α → β
  | [] => b₀
  | x :: xs => step x (foldr b₀ step xs)
```

In categorical terms:

* `List α` is the initial $F_\alpha$-algebra
* `(β, b₀, step)` is any other $F_\alpha$-algebra
* `foldr` is the unique morphism from the initial algebra to that target algebra

So every time you use `foldr`, you’re using the initiality of `List α` to collapse the list into a value.

UNDER CONSTRUCTION...





