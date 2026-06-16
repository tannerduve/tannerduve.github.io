---
layout: post
title: "Quantum Algorithms in Lean"
date: 2026-06-10 13:00:00 -0800
description: Formalizing and verifying textbook quantum algorithms in the query-combinator model
categories: Functional-Programming
tags: lean quantum-computing circuits formal-verification
thumbnail: assets/img/DJ.png
---

<!-- vscode-markdown-toc -->

## Table of Contents

- [Introduction](#Introduction)
- [Quantum Computing Basics](#QuantumBasics)
- [Part 1: The Quantum Query Model](#Part1)
  - [Deutsch-Jozsa Algorithm](#Deutsch-Jozsa)
- [Part 2: The Quantum Circuit Model](#Part2)
  - [GHZ Algorithm](#GHZ)
- [Conclusion](#Conclusion)
- [Acknowledgements](#Acknowledgements)
- [References](#References)

<!-- vscode-markdown-toc-config
    numbering=true
    autoSave=true
    /vscode-markdown-toc-config -->
<!-- /vscode-markdown-toc -->

## <a name='Introduction'></a>Introduction

I'm new to quantum computing, but in [how I've approached it](https://academic.oup.com/book/43710), I think that its compositional and algebraic nature is well suited for typed functional programming, and in particular I've become interested in using Lean to implement and prove things about quantum computation.

In this post I will show how to formalize basic textbook quantum algorithms in Lean. Our underlying computation framework is the query-combinator model from [Algolean](https://github.com/Shreyas4991/Algolean), by [Shreyas Srinivas](https://cispa.de/en/people/c01shsr). This model uses [free monads](https://tannerduve.github.io/blog/2025/freer-monad/) to allow users to write imperative programs in arbitrary computation models, verify their correctness using Lean's [mvcgen tactic](https://lean-lang.org/doc/reference/latest/The--mvcgen--tactic/), and analyze their complexity.

The query-combinator model is a research product that deserves better treatment than a blog post, so I won't explain in detail here. But from a user's standpoint the interface is as follows:

- Define a query type `Q : Type → Type`, where `Q α` is the type of basic operations of your computation model returning values of type `α`.
- Take the free monad over `Q`, which allows algorithms to be written in imperative-style `do` notation. This monad is denoted `Prog Q`
- Define a `Model`, which gives each query both an evaluation semantics `Q α → α` and a cost. The framework extends these compositionally to whole programs.
- Prove correctness statements about `P.eval M`, and complexity statements about `P.time M`.

For quantum algorithms, the queries will be quantum gates and oracle calls. The model interprets these queries as unitaries acting on an `n`-qubit state space, while the cost function counts oracle queries and treats the non-oracle gates as free.

This post explains two computation models and gives an example algorithm for each, with proofs of correctness and complexity.

## <a name='QuantumBasics'></a>Quantum Computing Basics

<details markdown="1">
<summary>Skip if you already know the basics of quantum computing.</summary>

A quantum system is modeled by a complex [Hilbert space](https://en.wikipedia.org/wiki/Hilbert_space); in finite dimensions, this is a complex vector space with an inner product. A qubit is the particular two-dimensional system $\mathbb{C}^2$, whose computational basis vectors are $\lvert0\rangle$ and $\lvert1\rangle$.

For an `n`-qubit system, the computational basis is indexed by functions `x : Fin n → Fin 2`, assigning a bit value to each qubit. The basis vectors are themselves indexed by these functions, and in Dirac notation $\lvert x\rangle$ denotes the one which is `1` at the entry indexed by `x` and `0` everywhere else.

A pure state of an `n`-qubit system is a unit vector

$$
|\psi\rangle = \sum_{x} \alpha_x |x\rangle, \qquad \sum_x |\alpha_x|^2 = 1
$$

whose complex coefficients $\alpha_x$ are called *amplitudes*.

Gates are *unitary* maps on this space, meaning linear maps that preserve length and so send unit vectors to unit vectors, keeping a state a valid state. A gate on a single qubit acts as the identity on the rest of the register. The basic operations of our quantum computation model are these gates.

One gate worth mentioning here is the Hadamard gate, $H\lvert b\rangle = \tfrac{1}{\sqrt{2}}\sum_{b'}(-1)^{b\cdot b'}\lvert b'\rangle$, which applied to every qubit of $\lvert0\cdots 0\rangle$ produces the uniform *superposition* $\tfrac{1}{\sqrt{2^n}}\sum_x \lvert x\rangle$, an equal-weighted combination of all $2^n$ basis states.

To extract classical information we *measure*, and the Born rule says measuring qubit `q` returns bit $b$ with probability $\sum_{x : x_q = b} \lvert\alpha_x\rvert^2$.

[Physlib](https://github.com/leanprover-community/physlib), the library we use for our semantic foundation, represents states as *density matrices*. A pure state $\lvert\psi\rangle$ becomes $\rho = \lvert\psi\rangle\langle\psi\rvert$, a gate $U$ acts by conjugation $\rho \mapsto U\rho U^\dagger$, and the Born rule reads $\Pr[b] = \mathrm{tr}(P_b\,\rho)$.

</details>

## <a name='Part1'></a>Part 1: The Quantum Query Model

To write algorithms we first need to define this computation model. Our first model counts a single resource, the number of times an algorithm calls an abstract oracle.

The primitive operations here are the basic quantum gates, as well as calls to the oracle. Each query denotes an element of `𝐔[Fin n → Fin 2]`, the unitaries on the `n`-qubit state space:

```lean
inductive QuantumQuery (n : ℕ) : Type → Type where
  /-- Hadamard gate on qubit `q`. -/
  | hadamard (q : Fin n) : QuantumQuery n (𝐔[Fin n → Fin 2])
  /-- Pauli-X (NOT) gate on qubit `q`. -/
  | pauliX (q : Fin n) : QuantumQuery n (𝐔[Fin n → Fin 2])
  /-- Pauli-Z gate on qubit `q`. -/
  | pauliZ (q : Fin n) : QuantumQuery n (𝐔[Fin n → Fin 2])
  /-- Controlled-NOT with distinct control and target. -/
  | cnot (control target : Fin n) (h : control ≠ target) :
      QuantumQuery n (𝐔[Fin n → Fin 2])
  /-- Phase gate `R(θ)` with rational parameter; semantics uses `exp(2πi·θ)`. -/
  | phase (q : Fin n) (θ : ℚ) : QuantumQuery n (𝐔[Fin n → Fin 2])
  /-- Oracle query: applies the phase oracle `|x⟩ ↦ (-1)^{f(x)}|x⟩`. -/
  | oracle : QuantumQuery n (𝐔[Fin n → Fin 2])
```

Queries are syntactic data used to denote unitaries. The actual unitaries come from the `Model`, which interprets each query denotationally, with complexity measured by the number of oracle calls, giving us a model of *quantum query complexity*

```lean
noncomputable def quantumModel (n : ℕ) (f : (Fin n → Fin 2) → Bool) :
    Model (QuantumQuery n) ℕ where
  evalQuery q := unitaryOf (gateOracle f) q
  cost
    | .oracle => 1
    | _ => 0
```

Where `unitaryOf` maps each gate to its `n`-qubit unitary.

Algorithms are written in `Prog (QuantumQuery n) (MState (Fin n → Fin 2))`, which is the free monad whose primitive operations are `QuantumQuery n`'s, returning as values a density matrix over the `n`-qubit basis (`MState` is Physlib's type of density matrices).

A query returns the unitary it denotes, but what an algorithm is actually updating at each step is the current quantum state of the register, a density matrix `ρ`. A small wrapper applies unitaries to sequentially update the state:

```lean
/-- Apply a gate to a density matrix, threading the result through `Prog`. -/
noncomputable def applyGate {n : ℕ}
    (q : QuantumQuery n (𝐔[Fin n → Fin 2]))
    (ρ : MState (Fin n → Fin 2)) :
    Prog (QuantumQuery n) (MState (Fin n → Fin 2)) :=
  FreeM.liftBind q fun U => pure (U ◃ ρ)
```

where `U ◃ ρ` is conjugation `U ρ U†`. This is what lets us write algorithms in imperative style:

```lean
let ρ ← applyGate (.hadamard 0) ρ₀
let ρ ← applyGate .oracle ρ
...
```

Given a program `P`, general free monad-ology extends the model compositionally, so that `P.eval M` is the final density matrix and `P.time M` is the total number of oracle queries.

After evaluation, we measure the final density matrix `P.eval M`, either a single qubit (`measureQubitPOVM q`) or the whole register, depending on the algorithm, with outcome probabilities given by the Born rule. Correctness statements then say that measuring the output yields the right answer with the right probability, and `P.time M` is small.

### <a name='Deutsch-Jozsa'></a>Deutsch-Jozsa Algorithm

The first algorithm we will implement is Deutsch-Jozsa, it's pretty simple but it's interesting in that it was one of the first examples of a quantum algorithm that is exponentially faster than any deterministic classical algorithm.

The problem it solves is a bit contrived, but it gave an early proof of concept that quantum computers can outperform classical ones, and its main trick reappears in more advanced algorithms like [Shor's](https://en.wikipedia.org/wiki/Shor%27s_algorithm).

#### Problem

We are given oracle access to a function $f : \{0,1\}^n \to \{0,1\}$, and are promised that $f$ is either *constant* (same value on every input) or *balanced* (true on exactly half of the inputs), and we must decide which.

Classically, a deterministic algorithm $2^{n-1}+1$ queries in the worst case, since after $2^{n-1}$ identical answers both cases are still possible. Quantumly we only need one.

#### Algorithm

Essentially what we do is make use of [superposition](https://en.wikipedia.org/wiki/Quantum_superposition). Applying Hadamards to $\lvert0\cdots 0\rangle$ spreads the register into an equal-weighted combination of all $2^n$ inputs, one oracle call changes the signs according to $f$, $\lvert x\rangle \mapsto (-1)^{f(x)}\lvert x\rangle$, and a second layer of Hadamards makes the signs interfere. The final amplitude on $\lvert0\cdots 0\rangle$ is their average

$$
\frac{1}{2^n}\sum_{x}(-1)^{f(x)},
$$

which is $\pm 1$ when $f$ is constant and $0$ when $f$ is balanced. So we measure the register, output "constant" if we see all zeros and "balanced" otherwise.

In Lean, the algorithm is a three-line `do` block. Recall that measurement is done outside the program, so we just return the final density matrix:

```lean
noncomputable def deutschJozsa (n : ℕ) :
    Prog (QuantumQuery n) (MState (Fin n → Fin 2)) := do
  let ρ ← applyHadamards (zeroRegisterState n)
  let ρ ← applyGate .oracle ρ
  applyHadamards ρ
```

#### Correctness and Complexity

First we prove a Hoare triple which describes the state the program produces. This state is the conjugation of $\lvert0\cdots 0\rangle\langle 0\cdots 0\rvert$ by $H^{\otimes n} O_f H^{\otimes n}$, which we write as `deutschJozsaResult n f`:

```lean
theorem deutschJozsa_spec (n : ℕ) (f : (Fin n → Fin 2) → Bool) :
    ⦃⌜True⌝⦄ deutschJozsa n
      ⦃⇓ ρ => ⌜ρ = deutschJozsaResult n f⌝⦄ := by
  mvcgen [deutschJozsa, Spec.applyHadamardLayer_spec]
```

The triple says that, from no assumptions, evaluating `deutschJozsa n` returns a density matrix `ρ` equal to `deutschJozsaResult n f`.

The proof invokes `mvcgen`, which walks the `do` block and discharges each step against its registered spec lemma.

We then compute the amplitude above and obtain the final correctness theorems, where `deutschJozsaZeroProbability n f` is the probability of measuring all zeros:

```lean
theorem deutschJozsaZeroProbability_eq_one_of_constant
    (hf : IsConstant f) : (deutschJozsaZeroProbability n f : ℝ) = 1

theorem deutschJozsaZeroProbability_eq_zero_of_balanced
    (hf : IsBalanced f) : (deutschJozsaZeroProbability n f : ℝ) = 0
```

Since the cost model charges `1` for oracle calls and `0` for everything else, the query complexity is straightforward:

```lean
theorem deutschJozsa_time (n : ℕ) (f) :
    (deutschJozsa n).time (quantumModel n f) = 1
```

This is what historically made this algorithm interesting, it requires a single oracle call, whereas deterministic classical algorithms have a lower bound of $2^{n-1}+1$ oracle calls.

## <a name='Part2'></a>Part 2: The Quantum Circuit Model

Our second model is the quantum circuit model. A circuit is a tree built from three constructors, single gates at the leaves, sequential composition on the same register, and parallel composition by tensoring disjoint registers:

```lean
inductive QuantumCircuit : ℕ → Type → Type where
  | gate {n : ℕ} (q : QuantumQuery n (𝐔[Fin n → Fin 2])) :
      QuantumCircuit n (CPTPMap (Fin n → Fin 2) (Fin n → Fin 2))
  | seq {n : ℕ} (c₁ c₂ : QuantumCircuit n
      (CPTPMap (Fin n → Fin 2) (Fin n → Fin 2))) :
      QuantumCircuit n (CPTPMap (Fin n → Fin 2) (Fin n → Fin 2))
  | par {m k : ℕ}
      (c₁ : QuantumCircuit m (CPTPMap (Fin m → Fin 2) (Fin m → Fin 2)))
      (c₂ : QuantumCircuit k (CPTPMap (Fin k → Fin 2) (Fin k → Fin 2))) :
      QuantumCircuit (m + k)
        (CPTPMap (Fin (m + k) → Fin 2) (Fin (m + k) → Fin 2))
```

A leaf is just a `QuantumQuery`, the same gates we used in the query model. The index type of a circuit is a `CPTPMap`, a completely positive trace-preserving map, which is the general type of a quantum channel from Physlib.

Channels are more general than unitaries, since they also describe measurement and noise, and taking a channel as the denotation is what lets the two composition operators fit together cleanly.

This is a real difference from the query model, where a program evaluated to an `MState`. Here a circuit denotes a channel, a map on states, and we apply it to the initial state afterward.

Each tree is interpreted into its channel by `toCPTP`:

```lean
noncomputable def toCPTP (oracle : OracleFamily) :
    {n : ℕ} → {ι : Type} → QuantumCircuit n ι → ι
  | _, _, .gate q => CPTPMap.ofUnitary (unitaryOf (oracle _) q)
  | _, _, .seq c₁ c₂ => (toCPTP oracle c₂).compose (toCPTP oracle c₁)
  | _, _, @QuantumCircuit.par m k c₁ c₂ =>
      let e := finFunSplitEquiv m k (Fin 2)
      CPTPMap.ofEquiv e.symm
        |>.compose ((toCPTP oracle c₁).prod (toCPTP oracle c₂))
        |>.compose (CPTPMap.ofEquiv e)
```

A gate becomes the channel that conjugates by its unitary, sequential composition is channel composition, and parallel composition tensors the two channels and reindexes the combined register through `finFunSplitEquiv`, which splits an `(m + k)`-qubit register into an `m`-qubit part and a `k`-qubit part.

The cose of a circuit is its depth, size, and number of oracle queries:

```lean
structure CircuitCost where
  depth : ℕ
  gates : ℕ
  oracleQueries : ℕ
```

Depth sums along sequential composition and takes the max along parallel composition, and gate count and oracle count just add up.

The model packages the semantics and the cost together:

```lean
noncomputable def quantumCircuitModel (n : ℕ) (oracle : OracleFamily) :
    Model (QuantumCircuit n) CircuitCost where
  evalQuery q := q.toCPTP oracle
  cost q := ⟨q.depthOf, q.size, q.oracleCount⟩
```

### <a name='GHZ'></a>GHZ Algorithm

Our example in the circuit model is the GHZ state preparation circuit. It makes a good first circuit-model example because it uses no oracle at all, only structure, one Hadamard followed by a series of CNOTs.

#### Problem

The Greenberger-Horne-Zeilinger state on `n` qubits is

$$
|\mathrm{GHZ}_n\rangle = \frac{1}{\sqrt{2}}\left(|0\cdots 0\rangle + |1\cdots 1\rangle\right),
$$

the standard first example of [entanglement](https://en.wikipedia.org/wiki/Quantum_entanglement), where the whole register is either all zeros or all ones. Deutsch-Jozsa was a decision problem, GHZ is a state-preparation problem. The task is to prepare this state on `n` qubits.

#### Algorithm

A Hadamard on qubit `0` puts it into $\tfrac{1}{\sqrt2}(\lvert0\rangle + \lvert1\rangle)$, and then a CNOT from qubit `0` into each later qubit copies that bit outward, so qubit `0` being `1` flips all the others to `1` as well. After these CNOTs the register is all zeros or all ones, entangled. In Lean the circuit is the tree

```lean
def ghzCircuit (n : ℕ) (hn : 1 < n) :
    QuantumCircuit n (RegisterChannel n) :=
  .seq
    (ghzHadamardGate (n := n) (by omega))
    (ghzCNOTChainAux n 1 (n - 2) (by omega) (by omega))
```

where `ghzCNOTChainAux` builds the linear chain `CNOT(0→1); CNOT(0→2); ...` by recursion on its length. We then package this as a program family over all register sizes, handling the degenerate small sizes separately: `n = 1` is just the one-qubit Hadamard, and `n = 0` returns the identity channel, since the circuit type has no empty-register leaf:

```lean
def ghzProgram : (n : ℕ) → Prog (QuantumCircuit n) (RegisterChannel n)
  | 0 => pure CPTPMap.id
  | 1 => ghzHadamardGate (n := 1) (by decide)
  | n + 2 => ghzCircuit (n + 2) (by omega)
```

#### Correctness and Complexity

Like we did with Deutsch-Jozsa, we can state what the program computes as a Hoare triple and discharge it with a single `mvcgen`. For `n + 2` qubits the program evaluates to the circuit's channel:

```lean
theorem ghzProgram_spec_succ_succ (n : ℕ) (oracle : OracleFamily) :
    letI : HasModel (QuantumCircuit (n + 2)) CircuitCost :=
      ⟨quantumCircuitModel (n + 2) oracle⟩
    ⦃⌜True⌝⦄ ghzProgram (n + 2)
      ⦃⇓ channel =>
        ⌜channel =
          QuantumCircuit.toCPTP oracle (ghzCircuit (n + 2) (by omega))⌝⦄ := by
  letI : HasModel (QuantumCircuit (n + 2)) CircuitCost :=
    ⟨quantumCircuitModel (n + 2) oracle⟩
  mvcgen [ghzProgram]
```

The triple says that evaluating `ghzProgram (n + 2)` returns a `channel` equal to `QuantumCircuit.toCPTP oracle (ghzCircuit (n + 2) ...)`, the denotation of the GHZ circuit tree. The `⇓ channel =>` binds that returned value so the postcondition can constrain it, and the `letI` lines just register which cost model the triple is taken over. With the program pinned down to the circuit's channel, correctness comes down to understanding what that channel does.

We prove correctness for every register size `n ≥ 2`. First we identify the channel as conjugation by the GHZ unitary `ghzUnitary`, the Hadamard on qubit `0` followed by the CNOT chain:

```lean
theorem ghzCircuit_toCPTP_apply (n : ℕ) (oracle : OracleFamily)
    (ρ : MState (Fin (n + 2) → Fin 2)) :
    QuantumCircuit.toCPTP oracle (ghzCircuit (n + 2) (by omega)) ρ =
      ghzUnitary (n + 2) (by omega) ◃ ρ
```

Applying this to the all-zeros input and computing entries, the output density matrix has support exactly on the `00...0`/`11...1` block, with all four entries there equal to `1/2`:

```lean
def IsGHZState (n : ℕ) (ρ : MState (Fin n → Fin 2)) : Prop :=
  ρ.m (ghzZero n) (ghzZero n) = (1 / 2 : ℂ) ∧
  ρ.m (ghzZero n) (ghzOne n) = (1 / 2 : ℂ) ∧
  ρ.m (ghzOne n) (ghzZero n) = (1 / 2 : ℂ) ∧
  ρ.m (ghzOne n) (ghzOne n) = (1 / 2 : ℂ) ∧
  ∀ i j,
    ((i ≠ ghzZero n ∧ i ≠ ghzOne n) ∨
      (j ≠ ghzZero n ∧ j ≠ ghzOne n)) →
      ρ.m i j = 0

theorem ghz_state_correctness {n : ℕ} (hn : 1 < n) (oracle : OracleFamily) :
    IsGHZState n (ghzOutput n oracle)
```

The two off-diagonal entries are the important part. A classical coin that outputs `00...0` or `11...1` each with probability `1/2` would have the same two diagonal entries, but its off-diagonal entries would be zero. Those coherence terms are what make this an entangled state rather than a classical mixture.

Measuring the register in the computational basis then gives `00...0` and `11...1` each with probability `1/2` and nothing else:

```lean
theorem ghz_readout_correctness {n : ℕ} (hn : 1 < n) (oracle : OracleFamily) :
    IsGHZDistribution n (ghzDistribution n oracle)
```

and the full statement bundles the prepared state together with its readout:

```lean
theorem ghz_correctness {n : ℕ} (hn : 1 < n) (oracle : OracleFamily) :
    IsGHZState n (ghzOutput n oracle) ∧
      IsGHZDistribution n (ghzDistribution n oracle)
```

Because GHZ never touches the oracle, the oracle parameter is irrelevant throughout, which is why every statement is universally quantified over `oracle`.

Finally, the cost. It is read straight off the circuit tree, with no oracle queries, depth `n`, and `n` gates:

```lean
theorem ghzCircuit_complexity (n : ℕ) (hn : 1 < n) :
    (ghzCircuit n hn).depthOf = n ∧
    (ghzCircuit n hn).size = n ∧
    (ghzCircuit n hn).oracleCount = 0
```

One Hadamard plus the `n - 1` CNOTs is `n` gates, and since they run one after another the depth is `n` as well. Lifting this to the program gives the same triple for `P.time`.

## <a name='Conclusion'></a>Conclusion

We built two quantum computation models on top of the query-combinator framework and verified one algorithm in each. The query model counts oracle calls, and Deutsch-Jozsa decides a promise problem in a single query, while deterministic classical algorithms need exponentially many.

The circuit model gives circuits structure and a richer cost of depth, size, and oracle count, which we use to verify the GHZ preparation circuit, both its linear cost and the entanglement in the state it produces.

In each case the algorithm is a short program in the free monad `Prog`, the `Model` supplies the semantics and the cost, and correctness follows from the general machinery, with `mvcgen` discharging the query-model proof and structural recursion handling the circuit cost. The same recipe should carry over to other models and algorithms, where the queries change but the framework around them stays the same.


## <a name='Acknowledgements'></a>Acknowledgements

Thanks to [Shreyas Srinivas](https://cispa.de/en/people/c01shsr) for developing the [Algolean](https://github.com/Shreyas4991/Algolean) framework on which our computation model is built, and to [Alex Meiburg](https://ohaithe.re) for his work formalizing quantum theory, which we use as our semantic foundation.

## <a name='References'></a>References

1. D. Deutsch and R. Jozsa, "Rapid solution of problems by quantum computation," *Proceedings of the Royal Society of London A*, vol. 439, no. 1907, pp. 553-558, 1992.
2. D. M. Greenberger, M. A. Horne, and A. Zeilinger, "Going beyond Bell's theorem," in *Bell's Theorem, Quantum Theory, and Conceptions of the Universe*, 1989.
3. M. A. Nielsen and I. L. Chuang, *Quantum Computation and Quantum Information*, Cambridge University Press, 2010.
