---
title: "Tutorial: A Verified Interpreter with Side Effects"
date: 2025-06-18 12:00:00 -0800
categories: [Formal Verification, Type Theory]
tags: [lean, formal-verification, free-monads, type-theory, tutorial]
math: true
hidden: true
---

## 1. <a name='Introduction'></a>Introduction

In this final section we will do a mini tutorial to show the power of the free monad by building an interpreter for an expression language with side effects. The key idea here is that the free monad lets us separate what we want to do (a syntactic description of effectful computation) from how we want to do it (interpreting and executing the effects semantically).

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

We begin by defining a tiny expression language, with integers, variables, addition, and division. We use the `Env` type to represent environments, which are just mappings of variables to values:

```lean
inductive Expr where
  | val : Int → Expr
  | var : String → Expr
  | add : Expr → Expr → Expr
  | div : Expr → Expr → Expr

abbrev Env := List (String × Int)
```

We also define three effect types: mutable state (for the environment), errors (for failed variable lookups or division by zero), and a trace log (for inspection or debugging):

```lean
inductive StateEff : Type → Type where
  | Get : StateEff Env
  | Put : Env → StateEff Unit

inductive ErrorEff : Type → Type where
  | Fail : String → ErrorEff Unit

inductive TraceEff : Type → Type where
  | Log : String → TraceEff Unit
```

We can then define a sum/coproduct of type constructors as follows:

```lean
inductive FSum (F G : Type → Type) (α : Type) where
  | inl : F α → FSum F G α
  | inr : G α → FSum F G α

infixl:50 "⊕" => FSum
```

And we define our overall effect signature as the nested sum:

```lean
abbrev Eff := StateEff ⊕ (ErrorEff ⊕ TraceEff)
```

Notice how free monads are extensible in their effects. Adding a new effect is simply constructing a new datatype and adding it to the Eff definition.

This type `Eff` is a pure description of the available commands in our language. Not what they do, just what kinds of actions exist. Our computations will now live in the type `FreeM Eff α`, which means they are pure syntax trees of abstract effects that eventually return a value of type `α`.

**Lifting Effects into the Syntax Tree**

To construct nodes in our effect AST, we define some helper functions that wrap each command in the FreeM monad. We first define a general way to lift an effect signature from `F` into its free monad `FreeM F`. This is the morphism `lift : F -> FreeM F` in the universal property diagram:

```lean
def lift (op : F ι) : FreeM F ι :=
  .liftBind op pure

def getEnv : FreeM Eff Env :=
  FreeM.lift (FSum.inl StateEff.Get)

def putEnv (e : Env) : FreeM Eff Unit :=
  FreeM.lift (FSum.inl (StateEff.Put e))

def fail (msg : String) : FreeM Eff Unit :=
  FreeM.lift (FSum.inr (FSum.inl (ErrorEff.Fail msg)))

def log (msg : String) : FreeM Eff Unit :=
  FreeM.lift (FSum.inr (FSum.inr (TraceEff.Log msg)))
```

**Writing a Program**

We can now write a little program. It logs a message, updates the environment, reads back a variable, and returns its increment:

```lean
def ex : FreeM Eff Int := do
  log "Starting"
  putEnv [("x", 10)]
  let env ← getEnv
  match env.find? (⋅.fst = "x") with
  | some (_, x) => pure (x + 1)
  | none => do fail "x not found"; pure 0
```

This "program" is constructing a tree of abstract effects independently of any execution or semantics. The calls to `log`, `putEnv`, `getEnv`, and fail are not doing anything yet, they are just nodes in a tree. When programs are represented as data structures you can do much more with them than just their operational interpretation, and you gain immense leverage and control over how you'd like to interpret them.

This separation between syntax and semantics is the core idea. We build up a value of type `FreeM Eff Int` that describes a program in terms of its desired behavior. This value is like an AST of effects. The tree is built using the constructors pure and bind, and the functorial action of the coproduct `⊕` lets us represent multiple kinds of effects simultaneously.

## 3. <a name='Interpreter'></a>Interpreter

To run a program written in `FreeM Eff α`, we must interpret its abstract syntax tree into a concrete computation. This involves defining a **catamorphism** — a recursive fold over the `FreeM` structure — into a semantic domain of effectful computations:

```lean
Env → Trace → Except String (α × Env × Trace)
```

Before we can fold the entire syntax tree, we need to define how to interpret each individual effect. This is done via a _handler_, which is a function that gives meaning to each primitive operation in the effect functor `Eff`.

```lean
Eff α → Env → Trace → Except String (α × Env × Trace)
```

This function interprets each effect label into our semantic domain of exceptions, states, traces:

```lean
abbrev Trace := List String

def effInterp : {α : Type} → Eff α → Env → Trace → Except String (α × Env × Trace)
  | _, .inl StateEff.Get => fun env trace => .ok (env, env, trace)
  | _, .inl (StateEff.Put newEnv) => fun _ trace => .ok ((), newEnv, trace)
  | _, .inr (.inl (ErrorEff.Fail msg)) => fun _ _ => .error msg
  | _, .inr (.inr (TraceEff.Log msg)) => fun env trace => .ok ((), env, trace ++ [msg])
```

This gives us the semantics for a single `Eff` node. But interpreting a full program requires recursively folding over the `FreeM` tree. Think of `effInterp` as the function which we will fold over the tree.

We define this fold using our catamorphism:

```lean
def cataFreeM {F : Type u → Type v} {α β : Type w}
  (pureCase : α → β)
  (bindCase : {ι : Type u} → F ι → (ι → β) → β)
  : FreeM F α → β
| .pure a => pureCase a
| .liftBind op k => bindCase op (fun x => cataFreeM pureCase bindCase (k x))
```

This is saying, given a type `β` with a `pureCase : α → β` and a `bindCase : {ι : Type u} → F ι → (ι → β) → β` (making it an algebra over the free monad functor), we define a function `cataFreeM : FreeM F α -> β`. This is indeed the catamorphism guaranteed by initiality of `FreeM F α`.

We define the carrier type of our effect algebra as:

```lean
abbrev EffAction (α : Type) := Env → Trace → Except String (α × Env × Trace)
```

Then we define the two parts of the algebra:

```lean
-- Handle pure values
def effPure {α} (a : α) : EffAction α :=
  fun env tr => .ok (a, env, tr)

-- Handle effectful operations and sequencing
def effStep {α} :
    {ι : Type} → Eff ι → (ι → EffAction α) → EffAction α
  | _, .inl StateEff.Get,        k => fun env tr => k env env tr
  | _, .inl (StateEff.Put σ),    k => fun _   tr => k () σ tr
  | _, .inr (.inl (ErrorEff.Fail msg)), _ =>
        fun _ _  => .error msg
  | _, .inr (.inr (TraceEff.Log msg)), k =>
        fun env tr => k () env (tr ++ [msg])
```

Finally, we combine the two cases into a full interpreter via our catamorphism `cataFreeM`:

```lean
def run {α} : FreeM Eff α → EffAction α :=
  cataFreeM effPure effStep
```

This catamorphism `run` is the unique morphism from `FreeM Eff α` to our effect algebra `EffAction α` which interprets computation trees of type `FreeM Eff α` by evaluating them and executing their effects concretely.

### 4. <a name='Verification'></a>Verification

Now that we have an interpreter, we can verify its correctness. What does correctness mean here?

In order to check that our interpreter is correct, we need some kind of semantics for our language, i.e., an assignment of meaning to our programs. In programming language theory, this is given as a formal relation that specifies when evaluation succeeds and what result it produces.

We'll define a _big-step operational semantics_ as an inductive relation, and then prove that the interpreter agrees with the semantics.

**Semantics**

We define a relation `EvalRel e env trace res` that says: under environment `env` and trace `trace`, expression `e` evaluates to result `res`. This result is either an error or a triple of the resulting value, environment, and trace. We also define a function `eval` which maps an expression to the effectful AST. Our correctness claim will then be that if `EvalRel e env trace res` holds (i.e., `e` evaluates to `res`), then our interpreter also returns `res` when run on the output of `eval e`.

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

The function `eval : Expr → FreeM Eff Int` constructs a tree of effects representing what should happen during evaluation from an expression. This is the object our interpreter consumes.

```lean
def eval : Expr → FreeM Eff Int
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

**What do we want to prove?**

We want to prove that `eval` followed by `run` gives the same result as the semantics. That is:

```lean
theorem eval_correct (e : Expr) (env : Env) (trace : Trace)
    (res : Except String (Int × Env × Trace))
    (h : EvalRel e env trace res) :
    run (eval e) env trace = res
```

**Proof**

We proceed by induction on the derivation of `EvalRel e env trace res`. In each case, we:

- Unfold the definition of `eval` for the given expression
- Use helper lemmas to simplify `run (p >>= k)`
- Match the result with the expected output

These two helper lemmas simplify `run (p >>= k)`:

```lean
theorem run_bind_ok {α β}
    {p : FreeM Eff α} {k : α → FreeM Eff β}
    {env env' : Env} {tr tr' : Trace} {v : α} (h : runEff p env tr = .ok (v, env', tr')) :
    runEff (p >>= k) env tr = runEff (k v) env' tr' := by ...
```

The above says if `p` succeeds with `v`, then `p >>= k` runs `k v` next.

```lean
theorem run_bind_err {α β}
    {p : FreeM Eff α} {k : α → FreeM Eff β}
    {env : Env} {tr : Trace} {msg : String} :
  runEff p env tr = .error msg →
  runEff (p >>= k) env tr = .error msg ...
```

This one says if `p` errors, then `p >>= k` errors with the same message.

Now we can prove the theorem.

```lean
theorem eval_correct (e : Expr) (env : Env) (trace : Trace)
    (res : Except String (Int × Env × Trace))
    (h : EvalRel e env trace res) :
    runEff (eval e) env trace = res := by
    induction' h
    · case val z env trace =>
      simp [eval, pure_eq_purePure, runEff, cataFreeM, effPure]
    · case var_found x env trace v h =>
      simp [runEff, eval, getEnv, bind_pure_comp, lift_def, cataFreeM, effStep, h, effPure]
    · case var_missing x env trace h =>
      simp [runEff, eval, bind, getEnv, fail, lift_def, cataFreeM, effStep, h]
    · case add e₁ e₂ env trace₁ trace₂ trace₃ v1 v2 env₂ env₃ h₁ h₂ ih₁ ih₂ =>
      simp [eval, bind]
      have step₁ := runEff_bind_ok (p := eval e₁ ) (k := fun v1 => do
        let v2 ← eval e₂
        pure (v1 + v2)) ih₁
      simp [bind] at step₁; simp [step₁]
      have step₂ := runEff_bind_ok (p := eval e₂) (k := fun v2 => pure (v1 + v2)) ih₂
      simp [bind] at step₂; simp [step₂]; congr
    · case div_ok e₁ e₂ env trace₁ trace₂ trace₃ v₁ v₂ env₂ env₃ v₂_ne_0 h₁ h₂ ih₁ ih₂  =>
      simp [eval, bind]
      have step₁ := runEff_bind_ok (p := eval e₁) (k := fun v1 => do
        let v2 ← eval e₂
        if v2 = 0 then do fail "divide by zero"; pure 0 else pure (v1 / v2)) ih₁
      simp [bind] at step₁; simp [step₁]
      have step₂ := runEff_bind_ok (p := eval e₂) (k := fun v₂ =>
        if v₂ = 0 then do fail "divide by zero"; pure 0 else pure (v₁ / v₂)) ih₂
      simp [bind] at step₂; simp [step₂, v₂_ne_0]
      congr
    · case div_zero e₁ e₂ env' trace₁ trace₂ trace₃ v₁ v₂ env₂ env₃ v₂_ne_0 h₁ h₂ ih₁ ih₂ =>
      simp [eval, bind]
      have step₁ := runEff_bind_ok (p := eval e₁) (k := fun v₁ => do let v₂ ← eval e₂; if v₂ = 0 then fail "divide by zero"; pure 0 else pure (v₁ / v₂)) ih₁
      simp [bind] at step₁; simp [step₁]
      have step₂ := runEff_bind_ok (p := eval e₂) (k := fun v₂ => if v₂ = 0 then (do fail "divide by zero"; pure 0) else pure (v₁ / v₂)) ih₂
      simp [bind] at step₂; simp [step₂, v₂_ne_0]
      simp [pure, fail, lift, runEff]
      congr
```

Now we have formally verified our interpreter agrees with our language semantics.

## 5. <a name='Conclusion'></a>Conclusion

Hopefully this article was informative and helpful in understanding free monads mathematically and gave you a glimpse of their usefulness in programming. This is the first blog post I've written so I'm hoping it was enjoyable. To review what we did:

- We introduced the concept of free objects in mathematics, starting with vector spaces, monoids, and groups.

- We defined the free monad categorically as the initial algebra of a particular functor, drawing analogy to the List type.

- In Haskell, we implemented the standard `FreeM f a` type and gave it a Monad instance.

- We learned about strict positivity in dependently typed proof assistants and why the classic `Free` monad fails in Lean

- We introduced the Freer monad as a strictly positive solution, and showed it forms a monad for any `F : Type -> Type`

- We talked about initial algebras and how catamorphisms are canonical interpreters for effect functors, and how universal morphisms interpret free monadic computations into other monads.

- We defined a small expression language with three effects: state, errors, and tracing, showed how effects can be represented as data structures using the FreeM monad, and wrote an interpreter for it as a catamorphism

- We showed how this separation between syntax and semantics enables flexibility in evaluating and interpreting effectful languages.

- We showed how to define an operational semantics and prove that the interpreter agrees with it.

All this code can be found [here](https://github.com/tannerduve/lean-playground/blob/main/LeanPlayground/freemonad.lean)

## 6. <a name='References'></a>References

- [nLab: Free Monad](https://ncatlab.org/nlab/show/free+monad)

- [CIS 5520 Lecture Notes on Freer Monads](https://www.seas.upenn.edu/~cis5520/22fa/lectures/stub/11-transformers/Freer.html)

- _The Dao of Functional Programming_, Bartosz Milewski (2025)

- [Serokell: Introduction to Free Monads](https://serokell.io/blog/introduction-to-free-monads)

- [Okmij : FreeM and Freer Monads: Putting Monads Back into Closet](https://okmij.org/ftp/Computation/free-monad.html)
