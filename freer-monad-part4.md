---
title: "Part 3: Universal Morphisms and Effect Handlers"
layout: single
permalink: /blog/freeer-monad/part4/
---

##  1. <a name='Introduction'></a>Introduction
As we recall from [part 1](/blog/freeer-monad/part1/), free objects are defined by left adjoints to forgetful functors, and can also be defined by a particular universal property. Universal properties are given by *universal arrows*: unique morphisms that characterize an object up to isomorphism. 

In this section we will apply the general universal property of the free object to our special case of monads. Specifically, we’ll discuss the free monad over a functor `F` is the monad that arises from freely generating effects described by `F`, with just enough structure to satisfy the monad laws and nothing else.

This point of view leads naturally to the concept of an effect handler, which is a function that interprets operations from `F` into a monad `M`. The universal property of the free monad ensures that any such handler extends uniquely to a monad morphism from the free monad into `M`. This morphism, in turn, acts as an interpreter for the entire computation.

<!-- vscode-markdown-toc -->
## Table of Contents

1. [Introduction](#Introduction)
2. [Free Monads as Free Objects](#FreeMonadAsFreeObject)
3. [Effect Handlers as Algebra Morphisms](#Handlers)
4. [The Universal Morphism](#UnivMorphism)
5. [Conclusion](#Conclusion)
6. [Exercise](#Exercise)
<!-- /vscode-markdown-toc -->


##  2. <a name='FreeMonadAsFreeObject'></a>Free Monads as Free Objects

The universal property of free objects, as we saw in part 1, the free object on some "basis" data $X$ is a structured object $X'$ which includes $X$, such that any map from $X$ into another structured object $G$ uniquely extends to a morphism from $X'$ to $G$. Diagrammatically:

<div style="text-align: center;">
  <span style="display: inline-block;">
    <script type="text/tikz">
      \begin{tikzcd}[scale=2, column sep=huge, row sep=huge]
        {X'} && G \\
        \\
        X
        \arrow["{\hat{h}}", dashed, from=1-1, to=1-3]
        \arrow["\iota", from=3-1, to=1-1]
        \arrow["h"', from=3-1, to=1-3]
      \end{tikzcd}
    </script>
  </span>
</div>


## 4. Effect Handlers as Algebra Morphisms

* Show how a handler is just a function `F α → M α` (or `∀ α, F α → M α`).
* Emphasize the analogy: the handler is a monad algebra (in the sense of Eilenberg-Moore).
* Show that this defines an `F`-algebra in `M`, and that the universal morphism preserves monadic structure.

---

## 5. The Universal Morphism

* Write the function:

  ```lean
  def interpret {F : Type u → Type v} [Monad M]
    (handler : ∀ {α}, F α → M α) : Free F α → M α
  ```
* Define it recursively, similar to the monadic bind:

  ```lean
  | pure a => pure a
  | lift op >>= k => handler op >>= (interpret ∘ k)
  ```
* Say: this is the universal morphism from `Free F` to any monad `M` given a handler.

---

## 6. Conclusion

* Compare catamorphisms vs universal morphisms:

  * Catamorphism: fold over structure.
  * Universal morphism: replay in another monad.
* Both are interpreters, but arise from distinct universal properties.

---

## 7. Exercise

* Implement `interpret` in Lean for the free monad you built in part 1.
* Then, interpret your program using `Option` as the monad (i.e., simulate failure).
* Bonus: use `State` or `IO` as the target monad.
