---
layout: post
title: "Tutorial: A Verified Interpreter"
date: 2025-06-18 12:00:00 -0800
description: Part of the free monads series
categories: Formal Verification, Type Theory
tags: lean, formal-verification, free-monads, type-theory, tutorial
series: free-monads
hidden: true
---

## 1. <a name='Introduction'></a>Introduction

To close the series, we'll build an interpreter for an expression language with algebraic effects. The free monad lets us separate *what* we want to do (a syntactic description of effectful computation) from *how* we want to do it (interpreting the effects).

<!-- vscode-markdown-toc -->

## Table of Contents

1. [Introduction](#Introduction)
2. [Language and Effects](#LanguageandEffects)
3. [Interpreter](#Interpreter)
4. [Verification](#Verification)
5. [Conclusion](#Conclusion)
6. [References](#References)

<!-- vscode-markdown-toc-config
	numbering=true
	autoSave=true
	/vscode-markdown-toc-config -->
<!-- /vscode-markdown-toc -->

## 2. <a name='LanguageandEffects'></a>Language and Effects

We begin by defining a tiny expression language with integers, variables, addition, and division. The `Env` type represents environments as mappings of variables to values.

```lean
inductive Expr where
  | val : Int → Expr
  | var : String → Expr
  | add : Expr → Expr → Expr
  | div : Expr → Expr → Expr

abbrev Env := List (String × Int)
```

We also define a single effect signature with constructors for mutable state (the environment), errors (failed variable lookups or division by zero), and a trace log (for inspection or debugging).

```lean
inductive EffectSig : Type → Type where
  | Get  : EffectSig Env
  | Put  : Env → EffectSig Unit
  | Fail : String → EffectSig Unit
  | Log  : String → EffectSig Unit
```

`EffectSig` is a description of the available commands in our language. Our computations will live in the type `FreeM EffectSig α`, syntax trees of abstract effects that eventually return a value of type `α`. Adding a new effect is just adding another constructor.

**Lifting Effects into the Syntax Tree**

To construct nodes in our effect AST, we define helpers that wrap each command in the FreeM monad. The generic `lift` is the morphism `lift : F → FreeM F` from the universal property diagram.

```lean
def lift (op : F ι) : FreeM F ι :=
  .liftBind op pure

def getEnv : FreeM EffectSig Env := FreeM.lift EffectSig.Get
def putEnv (e : Env) : FreeM EffectSig Unit := FreeM.lift (EffectSig.Put e)
def fail (msg : String) : FreeM EffectSig Unit := FreeM.lift (EffectSig.Fail msg)
def log (msg : String) : FreeM EffectSig Unit := FreeM.lift (EffectSig.Log msg)
```

**Writing a Program**

A little program that logs a message, updates the environment, reads back a variable, and returns its increment.

```lean
def ex : FreeM EffectSig Int := do
  log "Starting"
  putEnv [("x", 10)]
  let env ← getEnv
  match env.find? (⋅.fst = "x") with
  | some (_, x) => pure (x + 1)
  | none => do fail "x not found"; pure 0
```

This program isn't doing anything yet. It's a tree built from `pure` and `bind` whose nodes are abstract effect labels, a value of type `FreeM EffectSig Int` that describes *what* should happen, not *how*. Treating effects as data is what gives us the leverage to interpret the same program in different ways.

## 3. <a name='Interpreter'></a>Interpreter

To run a program of type `FreeM EffectSig α`, we fold its syntax tree into a concrete effectful computation. The semantic domain we'll fold into is just a function from an environment and trace to a possibly-failing tuple.

```lean
abbrev Trace := List String
abbrev EffAction (α : Type) := Env → Trace → Except String (α × Env × Trace)
```

The fold is just the recursor over `FreeM`, the analogue of `List.foldr` for the free monad.

```lean
def foldFreeM {F : Type u → Type v} {α β : Type w}
  (pureCase : α → β)
  (bindCase : {ι : Type u} → F ι → (ι → β) → β)
  : FreeM F α → β
| .pure a => pureCase a
| .liftBind op k => bindCase op (fun x => foldFreeM pureCase bindCase (k x))
```

Given a target type `β` with a `pureCase` for `pure` nodes and a `bindCase` for `liftBind` nodes, `foldFreeM` walks the syntax tree and produces a `β`.

Here are the two parts of the algebra over `EffAction`.

```lean
-- Handle pure values
def effPure {α} (a : α) : EffAction α :=
  fun env tr => .ok (a, env, tr)

-- Handle effectful operations and sequencing
def effStep {α} :
    {ι : Type} → EffectSig ι → (ι → EffAction α) → EffAction α
  | _, .Get,      k => fun env tr => k env env tr
  | _, .Put σ,    k => fun _   tr => k () σ tr
  | _, .Fail msg, _ => fun _   _  => .error msg
  | _, .Log msg,  k => fun env tr => k () env (tr ++ [msg])
```

`run` is then the corresponding fold.

```lean
def run {α} : FreeM EffectSig α → EffAction α :=
  foldFreeM effPure effStep
```

## 4. <a name='Verification'></a>Verification

To check our interpreter is correct, we need a semantics for the language. We'll define a _big-step operational semantics_ as an inductive relation, then prove the interpreter agrees with it.

**Semantics**

The relation `EvalRel e env trace res` says that under environment `env` and trace `trace`, expression `e` evaluates to result `res`, where `res` is either an error or a triple of value, environment, and trace.

```lean
inductive EvalRel : Expr → Env → Trace → Except String (Int × Env × Trace) → Prop where
| val :
    ∀ n env trace,
    EvalRel (.val n) env trace (.ok (n, env, trace))
| var_found :
    ∀ x env trace v,
    env.find? (·.fst = x) = some (x, v) →
    EvalRel (.var x) env trace (.ok (v, env, trace))
| var_missing :
    ∀ x env trace,
    env.find? (·.fst = x) = none →
    EvalRel (.var x) env trace (.error s!"unbound variable {x}")
| add :
    ∀ e1 e2 env trace₁ trace₂ trace₃ v1 v2 env₂ env₃,
    EvalRel e1 env trace₁ (.ok (v1, env₂, trace₂)) →
    EvalRel e2 env₂ trace₂ (.ok (v2, env₃, trace₃)) →
    EvalRel (.add e1 e2) env trace₁ (.ok (v1 + v2, env₃, trace₃))
| div_ok :
    ∀ e1 e2 env trace₁ trace₂ trace₃ v1 v2 env₂ env₃,
    v2 ≠ 0 →
    EvalRel e1 env trace₁ (.ok (v1, env₂, trace₂)) →
    EvalRel e2 env₂ trace₂ (.ok (v2, env₃, trace₃)) →
    EvalRel (.div e1 e2) env trace₁ (.ok (v1 / v2, env₃, trace₃))
| div_zero :
    ∀ e1 e2 env trace₁ trace₂ trace₃ v1 v2 env₂ env₃,
    v2 = 0 →
    EvalRel e1 env trace₁ (.ok (v1, env₂, trace₂)) →
    EvalRel e2 env₂ trace₂ (.ok (v2, env₃, trace₃)) →
    EvalRel (.div e1 e2) env trace₁ (.error "divide by zero")
```

The function `eval` builds a `FreeM EffectSig Int` tree describing what should happen during evaluation. This is the object our interpreter consumes.

```lean
def eval : Expr → FreeM EffectSig Int
  | .val n => pure n
  | .var x => do
      let env ← getEnv
      match env.find? (·.fst = x) with
      | some (_, v) => pure v
      | none => do
          fail s!"unbound variable {x}"
          pure 0
  | .add e1 e2 => do
      let v1 ← eval e1
      let v2 ← eval e2
      pure (v1 + v2)
  | .div e1 e2 => do
      let v1 ← eval e1
      let v2 ← eval e2
      if v2 = 0 then
        fail "divide by zero"
        pure 0
      else
        pure (v1 / v2)
```

**What we want to prove**

`eval` followed by `run` agrees with the semantics.

```lean
theorem eval_correct (e : Expr) (env : Env) (trace : Trace)
    (res : Except String (Int × Env × Trace))
    (h : EvalRel e env trace res) :
    run (eval e) env trace = res
```

**Proof sketch**

We proceed by induction on `EvalRel e env trace res`. Each case unfolds `eval`, applies one of two helper lemmas to simplify `run (p >>= k)`, and matches the result against the expected output. The helpers say bind preserves success and bind preserves errors.

```lean
theorem run_bind_ok {α β}
    {p : FreeM EffectSig α} {k : α → FreeM EffectSig β}
    {env env' : Env} {tr tr' : Trace} {v : α}
    (h : run p env tr = .ok (v, env', tr')) :
  run (p >>= k) env tr = run (k v) env' tr' := by ...

theorem run_bind_err {α β}
    {p : FreeM EffectSig α} {k : α → FreeM EffectSig β}
    {env : Env} {tr : Trace} {msg : String} :
  run p env tr = .error msg →
  run (p >>= k) env tr = .error msg := by ...
```

The base cases `val` and `var_found` close immediately by `simp`.

```lean
theorem eval_correct (e : Expr) (env : Env) (trace : Trace)
    (res : Except String (Int × Env × Trace))
    (h : EvalRel e env trace res) :
    run (eval e) env trace = res := by
  induction' h
  · case val z env trace =>
    simp [eval, pure_eq_purePure, run, foldFreeM, effPure]
  · case var_found x env trace v h =>
    simp [run, eval, getEnv, bind_pure_comp, lift_def,
          foldFreeM, effStep, h, effPure]
  · all_goals sorry  -- see below
```

The remaining cases (`var_missing`, `add`, `div_ok`, `div_zero`) follow the same pattern. Unfold `eval`, apply `run_bind_ok` once per subexpression to walk the result through the bind, then close with `congr`. The full proof is in the [repo](https://github.com/tannerduve/lean-playground/blob/main/LeanPlayground/freemonad.lean).

## 5. <a name='Conclusion'></a>Conclusion

That covers the arc of this series. Free objects in mathematics, the Freer construction that fixes strict positivity in Lean, the universal property that turns effect handlers into interpreters, and a small effect language interpreted by a fold over `FreeM` then verified against an operational semantics. Treating effects as data is what makes this kind of verification clean. You build a syntax tree of abstract effects and verify the interpreter as a separate object.

All the code is in the [repo](https://github.com/tannerduve/lean-playground/blob/main/LeanPlayground/freemonad.lean).

## 6. <a name='References'></a>References

- [nLab: Free Monad](https://ncatlab.org/nlab/show/free+monad)

- [CIS 5520 Lecture Notes on Freer Monads](https://www.seas.upenn.edu/~cis5520/22fa/lectures/stub/11-transformers/Freer.html)

- _The Dao of Functional Programming_, Bartosz Milewski (2025)

- [Serokell: Introduction to Free Monads](https://serokell.io/blog/introduction-to-free-monads)

- [Okmij : FreeM and Freer Monads: Putting Monads Back into Closet](https://okmij.org/ftp/Computation/free-monad.html)
