---
title: "Part 3: Universal Morphisms and Effect Handlers"
layout: single
permalink: /blog/freeer-monad/part3/
---

This post is under construction.

In the [previous section](/blog/freeer-monad/part2/), we explored free monads as initial algebras and used catamorphisms to define recursive interpreters. In this part, we shift to a different universal property — the **universal morphism** from free objects — and how it gives rise to a second, equally powerful notion of interpreter.

<!-- vscode-markdown-toc -->
## Table of Contents

1. [Introduction](#Introduction)
2. [Free Objects and Universal Morphisms](#Universal)
3. [Free Monads as Free Objects](#FreeMonadAsFreeObject)
4. [Effect Handlers as Algebra Morphisms](#Handlers)
5. [The Universal Morphism](#UnivMorphism)
6. [Conclusion](#Conclusion)
7. [Exercise](#Exercise)
<!-- /vscode-markdown-toc -->
```

---

### Section-by-section breakdown:

---

## 1. Introduction

* Brief recap of part 2: catamorphisms arise from initial algebras.
* Set up contrast: this time we focus on *free objects* in the categorical sense.
* Say: "The story is no longer about folding, but about replaying."

---

## 2. Free Objects and Universal Morphisms

* Define a *free object* over a functor \$U : D \to C\$ as a pair \$(F(a), \eta : a \to U(F(a)))\$ satisfying a universal property.
* Explain that a morphism out of the free object corresponds uniquely to an interpretation into any target object *with structure*.
* Link to monads: free monad over a functor \$F\$ is free for the forgetful functor `Monad → Endofunctor`.

---

## 3. Free Monads as Free Objects

* Explain that `Free F` is the free monad on `F`.
* Introduce the key data:

  * You give a natural transformation `F → M` (a handler).
  * You get a unique monad morphism `Free F → M`.
* Compare to part 2: instead of interpreting inductively, we’re interpreting by *replaying* the operations in another monad.

---

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
