---
layout: post
title: "Part 3: Universal Morphisms and Effect Handlers"
date: 2025-06-16 11:00:00 -0800
description: Part of the free monads series
categories: Formal Verification, Free Monads
tags: lean, free-monads, universal-properties, effect-handlers
hidden: true
tikzjax: true
---

## 1. <a name='Introduction'></a>Introduction

As we recall from [part 1](/blog/freer-monad/part1/), free objects are defined by left adjoints to forgetful functors, and can also be defined by a particular universal property. Universal properties are given by _universal arrows_: unique morphisms that characterize an object up to isomorphism. In [part 2](/blog/freer-monad/part2/), we talked about one particular universal property, and this part will focus on another.

In this section we will apply the general universal property of the free object to our special case of monads. The free monad over a type constructor `F` is the monad that arises from freely generating effects described by `F`, with just enough structure to satisfy the monad laws and nothing else.

This point of view leads naturally to the concept of an effect handler, which is a function that interprets operations from `F` into a monad `M`. The universal property of the free monad ensures that any such handler extends uniquely to a monad morphism from the free monad into `M`. This morphism, in turn, acts as an interpreter for the entire computation.

<!-- vscode-markdown-toc -->

## Table of Contents

1. [Introduction](#Introduction)
2. [Free Monads as Free Objects](#FreeMonadAsFreeObject)
3. [The Universal Morphism](#UnivMorphism)
4. [An Example](#Example)
5. [Conclusion](#Conclusion)
<!-- /vscode-markdown-toc -->

## 2. <a name='FreeMonadAsFreeObject'></a>Free Monads as Free Objects

The universal property of free objects, as we saw in part 1, says the free object on some "basis" data $X$ is a structured object $X'$ which includes $X$, such that any map from $X$ into another structured object $G$ uniquely extends to a morphism from $X'$ to $G$. Diagrammatically:

<script type="text/tikz">
  \begin{tikzcd}[column sep=huge, row sep=huge, labels={font=\normalsize}]
    {X'} \arrow[rr, dashed, "{\hat{h}}"] && G \\
    \\
    X \arrow[uu, "\iota"', pos=0.35] \arrow[uurr, "h"', pos=0.55]
  \end{tikzcd}
</script>

In the category of vector spaces for example, this intuitively says that if you have a function from a set $B$ to a vector space $W$, then this function can be extended uniquely (as a linear transformation) to the entire vector space $V_B$ with basis $B$. As we know from linear algebra, any linear transformation is uniquely defined by how it acts on a basis. This is the universal property in action.

Now what does this mean for monads? We know that our free monad generates a monad from a type constructor `F : Type -> Type`, so our "basis" data on which we freely generate our structured object (in this case, a monad) is `F` itself. Plugging things into the diagram, we get that for any type constructor `F` and a monad `M` with a map `h {a : Type} : F a -> M a`, `h` extends uniquely to a monad morphism `h' {a : Type} : FreeM F a -> M a`.

Intuitively, you can think of the morphism `h` as an _effect handler_ - it interprets each primitive operation described by `F` as a monadic computation in `M`. The universal property ensures that this effect handler uniquely lifts to a interpretation of entire programs written in the free monad, ie. computations of type `FreeM F`. That is, any computation of type `Free M a`, can be interpreted as a computation in `M` via a morphism `h' a : Free M a -> M a`. `h'` being a morphism, means it respects both `pure` and `bind` of the monads, ie:

```lean
h' (pure a) = pure a
h' (m >>= k) = h' m >>= fun x => h' (k x)
```

## 3. <a name='UnivMorphism'></a>The Universal Morphism

Let's formalize the universal property precisely. Recall, our `FreeM F` monad was defined inductively as a tree of computations:

```lean
inductive FreeM (F : Type u → Type v) (α : Type w)
  | pure : α → FreeM F α
  | liftBind {ι : Type u} (op : F ι) (cont : ι → FreeM F α) : FreeM F α
```

The universal property, more precisely, is as follows:

> Given any monad `M` and any function (an effect handler)
>
> ```lean
> f : ∀ α, F α → M α
> ```
>
> there exists a unique monad morphism
>
> ```lean
> f' : ∀ α, FreeM F α → M α
> ```
>
> such that
>
> ```lean
> f' (lift op) = f op
> ```

Here, `lift` is the inclusion map from our type constructor into the free monad. It lifts a primitive operation into its free monad structure.

Explicitly, we define this inclusion as:

```lean
def lift {F : Type u → Type v} {ι : Type u} (op : F ι) : FreeM F ι :=
  FreeM.liftBind op pure
```

The map `lift` takes a single operation from our basis `F` and wraps it as an effectful node inside `FreeM`.

The universal property then guarantees that for any monad `M` and any interpretation `f` from our effects to `M`, we can define our unique interpreter `liftM f`:

```lean
def liftM {M : Type u → Type w} [Monad M
    {α : Type u} : FreeM F α → ({β : Type u} → F β → M β) → M α
  | FreeM.pure a, _ => pure a
  | FreeM.liftBind op cont, interp => interp op >>= fun result => liftM (cont result) interp
```

This interpreter `liftM` traverses our computation tree. It interprets each effectful node using `interp` and recursively interprets the remaining computation.

The commutativity condition of the universal property explicitly states:

```lean
liftM f (lift op) = f op
```

In other words, interpreting an operation wrapped by `lift` using `liftM` is exactly the same as applying the effect handler `f` directly.

## 4. <a name='Example'></a>An Example

Let's illustrate this concretely with an example. Suppose we have a simple effect type describing state operations:

```lean
inductive StateF (σ : Type u) : Type u → Type u
  | get : StateF σ σ
  | set : σ → StateF σ PUnit
```

Using `lift`, we embed these operations into `FreeState σ α := FreeM (StateF σ) α`:

```lean
def get {σ : Type u} : FreeState σ σ := lift StateF.get

def set {σ : Type u} (s : σ) : FreeState σ PUnit := lift (StateF.set s)
```

Now suppose we want to interpret our `FreeState` computations into the standard state monad `StateM`. Our effect handler is straightforward:

```lean
def stateInterp {σ : Type u} : ∀ {α}, StateF σ α → StateM σ α
  | _, StateF.get => StateM.get
  | _, StateF.set s => StateM.set s
```

By the universal property, we uniquely lift this handler to interpret entire computations:

```lean
def toStateM {σ α : Type u} (comp : FreeState σ α) : StateM σ α :=
  liftM stateInterp comp
```

This interpreter maps our `FreeState` computations into the built-in `StateM` monad.

## 5. <a name='Conclusion'></a>Conclusion

The universal property of free monads provides a canonical interpreter with nice mathematical guarantees, ensuring that any choice of an effect handler uniquely determines how entire computations get interpreted. In this post we explored this universal property and showed an example in interpreting free computations into the state monad.

In practice, this means defining computations using `FreeM` is extremely flexible, as changing how we interpret effects is simply a matter of providing different handlers. The next and final section will be a tutorial on using the free monad to design a small DSL with mutable state, logging, and exceptions, and building a verified interpreter for the language.

## **Continue to Part 4 - A Tutorial**

[Continue to Part 4 - A Tutorial](/blog/2025/freer-monad-part4/)
