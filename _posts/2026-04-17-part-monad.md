---
layout: post
title: "Partiality in a Total Type Theory"
date: 2026-04-17 13:00:00 -0800
description: Modeling divergence and nontermination in Lean
categories: Formal-Verification
tags: lean category-theory domain-theory halting-problem monads
series_intro: part-monad
---

Lately I've been doing some work involving modeling and verifying imperative programs, and in particular imperative programs that may diverge (ie. not terminate), such as functions that contain loops that can run forever. 

In proof assistants like Lean we require that all functions are *total*, meaning any function which is definable in the core calculus will always terminate and return a value. This property is required for the consistency of the logic; if we could write nonterminating functions, we could write proofs of `False`, and our "proof" system would be useless.

It may seem like there's an issue here. If I'm working in a total proof assistant, how do I talk about programs which may not terminate? 

Lean's Mathlib offers an elegant way to do this, and its theory is rooted in Dana Scott's *domain theory*, a subject which brings together order theory and topology to give mathematical semantics to programming languages. 

This three-part post will cover how to model and reason about potentially-diverging computations in Lean. I will explain the basics of domain theory, explore the internals of Lean's `Part` monad, and formalize a useful theorem in domain theory. 

We will then use Lean to define a small imperative programming language with loops, give it denotational semantics using `Part`, and prove that these programs satisfy their specifications.

1. [Part 1 — Domain Theory Basics]({% post_url 2026-04-17-part-monad-1 %})
2. [Part 2 — Lean's `Part` Monad]({% post_url 2026-04-17-part-monad-2 %})
3. [Part 3 — Denotational Semantics of `IMP`]({% post_url 2026-04-17-part-monad-3 %})
