---
layout: post
title: "Verified Dynamic Programming with Σ-types in Lean"
date: 2025-05-21 12:00:00 -0800
description: Solving a competitive programming problem and proving it correct with dependent types
categories: Formal-Verification Algorithms
tags: lean dynamic-programming formal-verification dependent-types sigma-types
---

## 1. <a name='Introduction'></a>Introduction

If you've taken an algorithms class, you have likely seen dynamic programming, specifically a technique called _memoization_. Memoization works to optimize recursive algorithms by _caching_ the solutions to subproblems in a table, and when a subproblem is encountered, it queries the table instead of recomputing the solution. This gives us an exponential performance boost.

This blog post will show how to solve a dynamic programming problem using memoization in Lean, and verify its correctness against a specification. The technique used in the proof of correctness here is an interesting application of Lean's dependent types, and is generalized to work for any memoization algorithm. The idea came from a conversation with [GasStationManager](https://gasstationmanager.github.io) over at the [Lean Zulip chat](https://leanprover.zulipchat.com), who I credit with coming up with the general technique.

This should be pretty beginner friendly. Basic data structures+algorithms at the undergrad level. Lean experience is not necessary but is helpful for following code samples.

<!-- vscode-markdown-toc -->

## Table of Contents

1. [Introduction](#Introduction)
2. [Problem](#Problem)
3. [First Solution](#FirstSolution)
4. [Type Theory Interlude: Subtypes and Dependent Pairs](#Sigma)
5. [Improved Solution](#Solution)
6. [Conclusion](#Conclusion)
7. [Exercises](#Exercises)
8. [References](#References)

<!-- vscode-markdown-toc-config
  numbering=true
  autoSave=true
  /vscode-markdown-toc-config -->
<!-- /vscode-markdown-toc -->

## 2. <a name='Problem'></a>Problem

The problem we will be working on here is called [Bytelandian Gold Coins](https://www.hackerearth.com/practice/algorithms/dynamic-programming/state-space-reduction/practice-problems/algorithm/bytelandian-gold-coins/). The problem description is as follows:

> In Byteland they have a very strange monetary system. Each Bytelandian gold coin has an integer number written on it. A coin n can be exchanged in a bank into three coins: n/2, n/3 and n/4. But these numbers are all rounded down (the banks have to make a profit).
>
> You can also sell Bytelandian coins for American dollars. The exchange rate is 1:1. But you can not buy Bytelandian coins. You have one gold coin. What is the maximum amount of American dollars you can get for it?

The solution is classic DP. Observe that for any amount up to 8, we can't get more money by dividing into $n/2, n/3, n/4$. For any value, the minimum amount we can get out of it is $n$. We will compare this value with the value we get after dividing $n$ and select the bigger value.

## 3. <a name='FirstSolution'></a>First Solution

The solution is given by the following recurrence relation :

$$
f(n)=
\begin{cases}
n, & n \le 8,\\[6pt
\displaystyle
\max\!\bigl(n,\; f(\lfloor n/2\rfloor)+f(\lfloor n/3\rfloor)+f(\lfloor n/4\rfloor)\bigr), & n>8.
\end{cases}
$$

Before writing any code, here is the header we'll want to use:

```lean
import Std.Data.HashMap
open Std
```

We define the recurrence in Lean as follows:

```lean
def maxDollars_spec (n : Nat) : Nat :=
  if n ≤ 8 then
  -- Base case: for `n ≤ 8`, it's better to sell the coin directly.
    n
  else
  -- Recursive case: choose the maximum between selling the coin directly and exchanging it.
    max n (maxDollars_spec (n / 2) + maxDollars_spec (n / 3) + maxDollars_spec (n / 4))
```

This directly computes the maximum earnable amount. We will use this as our specification for proving our memoized solution is correct.

Now here is a memoized solution:

```lean
def maxDollarsMemo (n : Nat) : Nat :=
  let rec helperMemo (n : Nat) (memo : HashMap Nat Nat) : Nat × HashMap Nat Nat :=
      match memo.get? n with
      | some v => (v, memo)  -- already cached
      | none =>
        if n ≤ 8 then          -- base case: sell coin directly
          let memo' := memo.insert n n
          (n, memo')
        else
          -- recursive: compute best exchange value, memoizing along the way
          let (v1, memo1) := helperMemo (n / 2) memo
          let (v2, memo2) := helperMemo (n / 3) memo1
          let (v3, memo3) := helperMemo (n / 4) memo2
          let best := max n (v1 + v2 + v3)
          let memo' := memo3.insert n best
          (best, memo')
  (helperMemo n (HashMap.empty)).fst
```

This function defines a helper which caches the solutions to subproblems in a hashmap and at each recursive call, queries the hashmap for a stored value. It then calls the helper on the empty map and returns the `n`th value
_(Exercise : Rewrite this using a state monad to simulate mutating the hashmap instead of passing around a new one with each insertion)_

Now our correctness claim is as follows:

```lean
theorem memo_correct : ∀ (n : ℕ), maxDollarsMemo n = maxDollarsSpec n
```

That is, our memoized solution computes the recurrence correctly on every $n \in \mathbb{N}$.
Trying to prove this ends up being _very_ difficult. I invite the reader to try it out themselves and see where you get stuck. A good prover may figure it out. I attempted strong induction on $n$ to no avail and trying various approaches I kept getting stuck. The direct proof is indeed possible but the statement feels far too intuitively true to be worth this much effort. The key realization here as to what makes this proof difficult is that correctness relies on invariant properties of the data structure which we store our values in.

First off, we need to prove that the HashMap correctly computes subproblems, that is, that `get? x` always returns either `none` or a value which is equal to `maxDollars_spec x`. We also rely on the invariant that if the HashMap satisfies this property before the call to `helperMemo`, then it satisfies this property after the call to `helperMemo`. To prove this requires reasoning about the body of `helperMemo`.

There's a lot of logic to juggle here in our proof, but thankfully there is a better way. A Haskeller is likely familiar with the notion of refinement types. In Lean we call them subtypes. Subtypes provide a way to attach logical properties to data using a familiar set-builder-like notation, where we can refer to the type of all elements of some type `T` for which a particular property holds. An example of a subtype is `{n : ℕ // Even n}` - the subtype of `ℕ` consisting of all of the Even natural numbers. This is all just syntactic sugar for a dependent pair type, aka $\Sigma$-types. Let's explore these some more before moving on.

## 4. <a name='Sigma'></a>Type Theory Interlude: Subtypes and Dependent Pairs

This section is a brief detour into the theory of Lean's subtypes. This is optional but I find it valuable. In dependent type theory, $\Sigma$-types are a generalization of a product type, where the type of the second element in a pair can _depend_ on the value of the first element. In a non-dependent setting, the product $A \times B$ of two types $A$ and $B$ consists of all pairs $(a, b)$ where $a : A$ and $b : B$ - it's just the standard cartesian product. The dependent pair type generalizes this.

Suppose we have a type $A$ and a _family of types indexed by $A$_, denoted $B : A \to \mathcal{U}$ (where $\mathcal{U}$ denotes the universe of all types). Then the type $\sum_{(x : A)}B(x)$ consists of the pairs $(a, b)$ where $a : A$ and $b : B(a)$ - the _type_ of $b$ _depends_ on the _value_ of $a$. Note that the Cartesian product is exactly the special case where $B$ is constant, ie $\displaystyle\sum_{(x : A)}B = A \times B$.

Back to the original example, let's think about `{n : ℕ // Even n}` in these terms. Under the [propositions-as-types](https://en.wikipedia.org/wiki/Curry–Howard_correspondence) principle, the proposition `Even n` is of course just a type. But note that `Even n` is a _different_ proposition for every `n : ℕ` - that is, `Even` is a _family_ of types _indexed_ by `ℕ`. So, the type `{n : ℕ // Even n}` is exactly the $\Sigma$-type $\sum_{n : \mathbb{N}}\text{Even}(n)$, which consists of pairs $(n, P_n)$, where $P_n$ is a _proof_ that $n$ is Even.

For a primer on dependent type theory, see chapter 1 of [HoTT](https://www.cs.uoregon.edu/research/summerschool/summer14/rwh_notes/hott-book.pdf)

## 5. <a name='Solution'></a>Improved Solution

Now that we've introduced subtypes we will put them to use by writing a new memoized algorithm that, in some sense, proves itself. Remember part of our correctness proof is showing that the HashMap's `get? x` method always returns a `y` such that `maxDollars_spec x = y`. What if, to guarantee this, we write a new version of `get?` so that `get? x` returns a `y` in the subtype `{y : ℕ // maxDollars_spec x = y}`? To do this, we can just subtype the data which our HashMap stores.

For the memoization, the property we want to hold is: for a pair `(k, v)` stored in your table, `f k = v` where `f` is the recursive function you are proving equivalence to (in our case, `f` is the the recurrence `maxDollars_spec`).

Now the implementation is as follows. We begin with a very general definition: a pair of values with a property attached to it:

```lean
def cell (f : α → β) := {c: α × β // f c.fst = c.snd}
```

That is, given a function `f : α → β`, for example the recurrence `maxDollars_spec` above, `cell f` is the type of all pairs `(a, b) : α × β` such that `f a = b`

Our new HashMap, `PropMap`, stores keys of type `α` and values of type `cell f` whose first element is equal to the key:

```lean
abbrev PropMap [BEq α][Hashable α] [LawfulBEq α] (f : α → β) :=
  HashMap α (cell f)
```

Now we can define `get?` with the guarantee we are looking for:

```lean
def PropMap_get? [BEq α][Hashable α] [LawfulBEq α] (ft : α → β) (hm : PropMap ft) (a : α) : Option { b : β // ft a = b } :=
  match hf : hm.get? a with  -- Attempt to get the value associated with `a` in the map.
  | none => none            -- If not found, return `none`.
  | some x =>
    if heq : a == x.val.fst then  -- Check if the key `a` matches `x.val.fst`.
      have : ft a = x.val.snd := by
        have hx := x.property       -- Extract the proof that `ft x.val.fst = x.val.snd`.
        rw [beq_iff_eq] at heq      -- Propositional equality from boolean equality
        rw [← heq] at hx            -- Replace `x.val.fst` with `a` using `heq`.
        exact hx                    -- Conclude that `ft a = x.val.snd`.
      pure ⟨ x.val.snd, this ⟩     -- Return the value and proof as `some`.
    else
      none  -- If the keys don't match (shouldn't happen), return `none`.
```

As well as an insertion function:

```lean
def PropMap_insert [BEq α][Hashable α] [LawfulBEq α] (ft : α → β) (hm : PropMap ft) (k : α) (v : β) (h : ft k = v) : PropMap ft :=
  let cell : { c : α × β // ft c.fst = c.snd } := ⟨(k, v), h⟩  -- Create the cell with proof.
  hm.insert k cell  -- Insert the cell into the map at key `k`.
```

And now we can define our recursive helper:

```lean
def helper (n : Nat) (memo : PropMap maxDollars_spec) :
  { v : Nat // maxDollars_spec n = v } × PropMap maxDollars_spec :=
  match PropMap_get? maxDollars_spec memo n with
  | some result =>
    -- If `n` is already in the memoization map, return the cached value and the memo.
    -- `result` has type `{ v : Nat // maxDollars_spec n = v }`.
    (result, memo)
  | none =>
    if h : n ≤ 8 then
      -- Base case: for `n ≤ 8`.
      let v := n
      let h_spec : maxDollars_spec n = v := by simp [maxDollars_spec, h
      -- Prove that `maxDollars_spec n = n` using simplification.
      let memo' := PropMap_insert maxDollars_spec memo n v h_spec
      -- Insert `(n, v)` with proof into the memoization map.
      (⟨v, h_spec⟩, memo')
    else
      -- Recursive case: compute the values for `n / 2`, `n / 3`, and `n / 4`.
      let (r1, memo1) := helper (n / 2) memo
      let (r2, memo2) := helper (n / 3) memo1
      let (r3, memo3) := helper (n / 4) memo2
      -- `r1`, `r2`, `r3` are of type `{ v : Nat // maxDollars_spec (n / x) = v }`. Basically an induction hypothesis.
      -- `memo3` is the updated memoization map after all recursive calls.
      let exchangeSum := r1.val + r2.val + r3.val  -- Sum the values obtained from recursion.
      let v := max n exchangeSum  -- Decide whether to sell `n` directly or exchange it.

      -- **Construct the proof that `maxDollars_spec n = v`**
      have h_spec : maxDollars_spec n = v := by
        unfold maxDollars_spec         -- Expand `maxDollars_spec n`.
        rw [if_neg h]                  -- Since `n > 8`, use the recursive case.
        rw [r1.property, r2.property, r3.property

      -- Replace recursive calls with their computed values using the proofs from `r1`, `r2`, `r3`.
      let memo' := PropMap_insert maxDollars_spec memo3 n v h_spec
      -- Insert the computed value and its proof into the memoization map.
      (⟨v, h_spec⟩, memo')  -- Return the computed value with proof and the updated memo.
```

Look here. Subtypes require proofs that their value satisfies their logical property. Thus each time our algorithm computes a value `v` to go in our table, we also compute a proof that `v` is computed correctly according to `maxDollars_spec`. We are interleaving code and proof and essentially proving correctness _inside the algorithm itself_.

And finally, here is our main function:

```lean
def maxDollars (n : Nat) : Nat :=
  (helper n (HashMap.empty)).1
```

We've embedded the proof into the algorithm itself: every computed value is stored together with a proof that it satisfies the spec. So to prove correctness for any n, we just apply the function — its type guarantees that the result equals maxDollars_spec n:

```lean
theorem maxDollars_spec_correct : ∀ n, maxDollars n = maxDollars_spec n := by
  intro n
  unfold maxDollars
  let ⟨v, h_spec⟩ := (helper n HashMap.empty).1
  exact h_spec.symm
```

And we're done. The algorithm has been verified.

## 5. <a name='Conclusion'></a>Conclusion

My goal here was to share what I learned from this technique and show how it can be applied to a particular problem. I also hope the reader came away understanding subtypes from the perspective of dependent type theory. I find intertwining code with proof in this way really cool and the people I've shown this to felt the same.

To review what we did:

- We introduced the Bytelandian Gold Coins problem and wrote a basic recursive specification using a natural recurrence relation.

- We implemented a naive memoized version using a `HashMap`, and discussed why proving its correctness directly is tough due to the difficulty of reasoning about data structure invariants.

- We took a detour into type theory to study subtypes and \$\Sigma\$-types as a way to attach logical properties to data.

- We defined a new form of memoization table (`PropMap`) that stores not just computed values, but also _proofs_ that they were computed correctly with respect to the spec.

- We rewrote the algorithm so that correctness was proven incrementally, at every step, as a side effect of evaluation - embedding the proof _into_ the recursion.

- We ended with a trivial top-level proof: correctness follows directly from the structure of the implementation.

All this code is available at [this repo](https://github.com/tannerduve/coins)

## 6. <a name='Exercises'></a>Exercises

Each of the following DP problems can be solved using the same framework introduced in this post: define a recurrence relation as a specification, write a memoized implementation that returns values paired with correctness proofs via subtypes, and prove the top-level function computes the intended result.

Try implementing and verifying your favorite(s) of the following:

- **Rod Cutting**
  Given a rod of length `n` and a list of prices `p : List ℕ` where `p[i]` is the price of a rod of length `i + 1`, define:

  $$
  r(n) = \max_{1 \le i \le n} (p[i{-}1] + r(n - i))
  $$

  Implement `rodCut : ℕ → ℕ` using a memoization table and prove correctness

- **0/1 Knapsack**
  Given `n` items with weights `w : Fin n → ℕ`, values `v : Fin n → ℕ`, and a maximum capacity `C`, define:

  $$
  \text{knapsack}(i, c) =
  \begin{cases}
  0, & i = n \\
  \text{knapsack}(i+1, c), & w[i] > c \\
  \max(\text{knapsack}(i+1, c),\ v[i] + \text{knapsack}(i+1, c - w[i])), & \text{otherwise}
  \end{cases}
  $$

  Implement and verify `knapsack : ℕ → ℕ` using a memo table indexed by item and capacity.

- **Levenshtein Distance**
  Given two strings `s` and `t`, define their edit/Levenshtein distance:

  $$
  \text{dist}(i, j) =
  \begin{cases}
  i, & j = 0 \\
  j, & i = 0 \\
  \min\!\left(
     \text{dist}(i{-}1, j) + 1,\;
     \text{dist}(i, j{-}1) + 1,\;
     \text{dist}(i{-}1, j{-}1) + \text{cost}
  \right), & \text{otherwise}
  \end{cases}
  $$

  where `cost = 0` if `s[i-1] = t[j-1]` and `1` otherwise. Implement and verify `editDist : String → String → ℕ`.

In each case, define the specification as a recursive function, then write a subtype-verified implementation using a `PropMap` to cache and prove subproblem results. Your goal is a final theorem of the form:

```lean
theorem algorithm_correct : ∀ input, algorithm input = spec input
```

## 7. <a name='References'></a>References

[Proving Memoization in Lean, And Teaching it to Sonnet](https://gasstationmanager.github.io/ai/2024/12/03/memoization1.html), GasStationManager
