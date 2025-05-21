---
title: "Verifying Memoization with Σ-types in Lean"
layout: single
permalink: /blog/memoization-sigma/
---

🚧 Under construction

This post shows how to verify a **dynamic programming solution** inside Lean with a novel use of dependent types.

We’ll:
- solve a competitive programming problem with a memoization table,
- use `Σ`-types (dependent pairs) to pair table entries with proofs of their correctness,
- and **verify correctness as we go**, encoding the DP invariant into the structure of the computation itself.
