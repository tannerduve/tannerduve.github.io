---
title: "Chicken-pi: A Toy Proof Assistant in Haskell"
layout: single
permalink: /blog/chicken-pi/
---

🚧 Under construction 🐔

This post will walk through the design and implementation of `chicken-pi`, a lightweight proof assistant written in Haskell that serves as a minimal implementation of the **Calculus of Inductive Constructions (CIC)**.

Chicken-pi supports:

- dependent inductive types and pattern matching,
- a cumulative universe hierarchy (`Prop`, `Set`, `Type i`),
- a syntactic guarded recursion check for `fix`.

Chicken-pi is primarily inspired by Coq but uses concepts from Lean when convenient (eg. annotated type universes)

The project takes a small polymorphic lambda calculus [`pi-forall version 2`](https://github.com/sweirich/pi-forall/tree/2023/version2), and extends it with the above constructs to work as a full-fledged proof assistant.

This post will focus on:
- the structure of the type system and universes,
- the type checker (aka proof checker ;),
- and the design decisions involved in adapting CIC to a minimal core.
