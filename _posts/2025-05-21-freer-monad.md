---
title: "The Free-er Monad"
layout: single
permalink: /blog/freer-monad/
---

Free monads provide a way to represent effectful sequential programs as pure syntactic data, separate from their interpretation. You describe *what* should happen as an abstract tree of effects, leaving open *how* you want it to happen. By decoupling syntax from semantics like this you gain full control over how programs are evaluated and interpreted - for example we could interpret a syntax tree in multiple ways:

- Run it directly
- Pretty print it
- Analyze it statically

Each of these corresponds to a different interpreter. This approach also allows effects to be combined without you having to get tangled up in monad transformers. *Freer* monads are a flexible generalization of free monads that make combining and interpreting effects even easier.

This three-part series will introduce the freer monad in Lean — Part 1 will introduce the categorical theory and motivation of the free monad and walk through its implementation in Lean. In part 2 we will further explore some theory and study initial algebras and catamorphisms, and how they give rise to canonical interpreters for effectful computation trees. In part 3 we will use what we've learned to build and verify a real interpreter for a small language, making elegant use of freeness to combine effectful computations.

This series assumes you know basic concepts from both category theory and functional programming, including functors, monads, and inductive datatypes.

1. [Part&nbsp;1 — Defining the Free Monad in Lean](/blog/freer-monad/part1/)
2. [Part&nbsp;2 — Catamorphisms, Interpreters, and Universal Properties](/blog/freer-monad/part2/)
3. [Part&nbsp;3 — Tutorial: A Verified Interpreter with Side Effects](/blog/freer-monad/part3/)