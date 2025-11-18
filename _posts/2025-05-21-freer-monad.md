---
layout: post
title: "The Free Monad: A Four-Part Series"
date: 2025-05-21 13:00:00 -0800
description: A four-part series on free monads in Lean
categories: Formal-Verification Free-Monads
tags: lean free-monads category-theory effects
---

Free monads provide a way to represent effectful sequential programs as pure syntactic data, separate from their interpretation. You describe _what_ should happen as an abstract tree of effects, leaving open _how_ you want it to happen. By decoupling syntax from semantics like this you gain full control over how programs are evaluated and interpreted - for example we could interpret a syntax tree in multiple ways:

- Run it directly
- Pretty print it
- Analyze it statically

Each of these corresponds to a different interpreter. This approach also allows effects to be combined without you having to get tangled up in monad transformers. _Freer_ monads are a flexible generalization of free monads that make combining and interpreting effects even easier.

This four-part series will introduce the freer monad in Lean — Part 1 will introduce the categorical theory and motivation of the free monad and walk through its implementation in Lean. In part 2 we will further explore some theory and study initial algebras and catamorphisms, and how they give rise to canonical interpreters for effectful computation trees. In part 3 we will study the universal property of free monads and what it provides for us as programmers. Finally in part 4, we will use what we've learned to build and verify a real interpreter for a small language, making elegant use of freeness to combine effectful computations.

This series assumes you know basic concepts from both category theory and functional programming, including functors, monads, and inductive datatypes.

1. [Part 1 — Defining the Free Monad in Lean]({% post_url 2025-06-16-freer-monad-part1 %})
2. [Part 2 — Initial Algebras, Catamorphisms, and Interpreters]({% post_url 2025-06-16-freer-monad-part2 %})
3. [Part 3 — Universal Morphisms and Effect Handlers]({% post_url 2025-06-16-freer-monad-part3 %})
4. [Part 4 — Tutorial: A Verified Interpreter with Side Effects]({% post_url 2025-06-18-freer-monad-part4 %})
