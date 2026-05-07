---
layout: post
title: "The Free Monad"
date: 2025-05-21 13:00:00 -0800
description: A three-part series on free monads in Lean
categories: Formal-Verification Free-Monads
tags: lean free-monads category-theory effects
series_intro: free-monads
thumbnail: assets/img/free-monad-thumb.png
---

In functional programming, monads are how we structure and sequence computations with side effects like state, IO, or failure. Each monad bakes its semantics into its definition. `State` updates a state, `IO` talks to the world, `Maybe` short-circuits on failure. *Free* monads provide a bit more freedom, in that they let you write effectful programs as pure data, without committing to a particular interpretation of the effects. You can write monadic programs in `do` notation, describing some sequence of effects, and only decide what they mean later. For example, these are just a few things you can do with a program-as-data:

- Run it directly
- Pretty print it
- Analyze it statically
- Track its resource usage

Each of these corresponds to a different interpreter. This approach also allows effects to be combined without you having to get tangled up in monad transformers.

This three-part series will introduce the free monad in Lean. In this first part we will introduce and implement the free monad from first principles, and discuss some of the finesse involved in implementing it in a proof assistant like Lean, compared to a language like Haskell.

In part 2 we will study the universal property of free monads and what it provides for us as programmers. Finally in part 3, we will use what we've learned to build and verify a real interpreter for a small language, making elegant use of freeness to combine effectful computations.

This series assumes you know basic concepts from both category theory and functional programming, including functors, monads, and inductive datatypes. All of the code in this blog post has been packaged into a library, now merged into [CSlib](https://github.com/leanprover/cslib/tree/main/Cslib/Foundations/Control/Monad).[^zklean]

[^zklean]: The free monad construction we develop in this series has seen real industrial use. Galois's [zkLean](https://github.com/GaloisInc/zkLean) is a Lean DSL for formally verified zero-knowledge proofs, built on top of this construction.

1. [Part 1 — Defining the Free Monad in Lean]({% post_url 2025-06-16-freer-monad-part1 %})
2. [Part 2 — Universal Morphisms and Effect Handlers]({% post_url 2025-06-16-freer-monad-part2 %})
3. [Part 3 — Tutorial: A Verified Interpreter with Side Effects]({% post_url 2025-06-18-freer-monad-part3 %})
