---
title: "Free-er Monad — Part 2: Catamorphisms, Interpreters, and Universal Proprties"
layout: single
permalink: /blog/freeer-monad/part2/
---

In the [last section](/blog/freeer-monad/part1/), we introduced the free monad and implemented it in Lean. In this section we will look into the theory a bit more deeply, by understanding the notions of algebra and universality.

##  1. <a name='Introduction'></a>Introduction: Two Universal Properties

In this part, we will explore two related but distinct universal constructions, both of which will give rise to unique morphisms that, as programmers, we can think of as "interpreters" in different senses. We will be looking at
- **Catamorphisms** from initial algeberas, and
- **Universal morphisms** from free objects

We'll first examine how free monads act as initial algebras, giving us catamorphisms into other algebras. Then, we'll revisit the notion of a free object from part 1, and explain how the free monad induces a universal morphism into any monad equipped with an effect handler. Both of these yield interpreters: catamorphisms interpret by folding data, while universal morphisms interpret by replaying abstract operations in a concrete monad.

<!-- vscode-markdown-toc -->
## Table of Contents

1. [Introduction](#Introduction)
2. [Initial Algebras and Inductive Types](#InitialAlgebras)
3. [Free Monads as Initial Algebras](#FreeMonads)
4. [Interpreters as Catamorphisms](#Cata)
5. [The Universal Morphism](#UniversalMorphisms)
6. [Interpreters as Universal Morphisms](#Universal)

<!-- vscode-markdown-toc-config
	numbering=true
	autoSave=true
	/vscode-markdown-toc-config -->
<!-- /vscode-markdown-toc -->

##  1. <a name='InitialAlgebras'></a>Initial Algebras and Inductive Types

Algebra is about manipulating formal expressions. Consider algebraic expressions like $2(x + y)$ or $ax^2 + bx + c$. Notice that there are infinitely many of them, yet only a finite number of rules for making them. This suggests that the rules are used recursively. Let's examine this connection between algebra and recursion a bit, from the perspective of category theory.

**Algebras and their morphisms**  
Let $F : C \to D$ be a functor. An *algebra* over $F$ is a pair $(A, \alpha)$ where $\alpha : FA \to A$.

Given $F$-algebras $(A, \alpha)$ and $(B, \beta)$, $\phi : A \to B$ is an $F$-algebra morphism iff the following diagram commutes:
<div style="text-align: center;">
  <script type="text/tikz">
    \begin{tikzcd}
    	FA && A \\
    	\\
    	FB && B
    	\arrow["\alpha", from=1-1, to=1-3]
    	\arrow["Ff"', from=1-1, to=3-1]
    	\arrow["f", from=1-3, to=3-3]
    	\arrow["\beta"', from=3-1, to=3-3]
    \end{tikzcd}
  </script>
</div>

$F$-algebras and their morphisms form a category, and the initial object in this category is called the *initial algebra*. That is, $(A, \alpha)$ is an initial $F$-algebra iff for any $F$-algebra $(B, \beta)$, there is a unique morphism $\phi : (A, \alpha) \to (B, \beta)$

**Inductive Types**
As it turns out, in terms of categorical semantics, an inductive type is a type whose interpretation is given by an initial algebra of an endofunctor.





