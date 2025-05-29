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

##  1. <a name='Introduction'></a>Introduction
If you've taken an algorithms class, you have likely seen dynamic programming, specifically a technique called *memoization*. Memoization works to optimize recursive algorithms by *caching* the solutions to subproblems in a table, and when a subproblem is encountered, it queries the table instead of recomputing the solution. This gives us an exponential performance boost. 

This blog post will show how to solve a particular dynamic programming problem using memoization in Lean, and verify its correctness against a specification. The proof of correctness here is an interesting application of Lean's dependent types that allows algorithms to compute their own correctness proofs.

## 2. <a name='Problem'></a>Problem
The problem we will be working on here is called [Bytelandian Gold Coins](https://www.hackerearth.com/practice/algorithms/dynamic-programming/state-space-reduction/practice-problems/algorithm/bytelandian-gold-coins/). The problem description is as follows:

> In Byteland they have a very strange monetary system. Each Bytelandian gold coin has an integer number written on it. A coin n can be exchanged in a bank into three coins: n/2, n/3 and n/4. But these numbers are all rounded down (the banks have to make a profit).
> 
> You can also sell Bytelandian coins for American dollars. The exchange rate is 1:1. But you can not buy Bytelandian coins. You have one gold coin. What is the maximum amount of American dollars you can get for it?

The solution is classic DP. Observe that for any amount up to 8, we can't get more money by dividing into $n/2, n/3, n/4$. For any value, the minimum amount we can get out of it is $n$. We will compare this value with the value we get after dividing $n$ and select the bigger value. 

## 3. <a name='FirstSolution'></a>First Solution

To begin we can easily define the recursive function which computes the maximum amount without memoization:
```lean
def maxDollars_spec (n : Nat) : Nat :=
  if n ≤ 8 then
  -- Base case: for `n ≤ 8`, it's better to sell the coin directly.
    n
  else
  -- Recursive case: choose the maximum between selling the coin directly and exchanging it.
    max n (maxDollars_spec (n / 2) + maxDollars_spec (n / 3) + maxDollars_spec (n / 4))
```
This directly computes the maximum earnable amount but is non-memoized and is thus slow. We will use this as our specification later on for proving our memoized solution is correct.

Here is a memoized solution:
```lean
def maxDollarsMemo (n : Nat) : Nat :=
  let rec helperMemo : Nat → HashMap Nat Nat → Nat × HashMap Nat Nat
    | n, memo =>
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
  (helperMemo n (HashMap.emptyWithCapacity)).fst
```
This function defines a helper which does exactly what memoization is supposed to do. It caches the solutions to subproblems in a hashmap and at each recursive call, queries the hashmap for a stored value. It then calls the helper on the empty map and returns the `n`th value

(Exercise : Rewrite this using a state monad to simulate mutating the hashmap instead of passing around a new one with each insertion)



