--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.

import Mathlib

namespace LeanW26

/-
Automated Mathematics
===
Luz Elena Grisales Gómez and Nat Hurtig (TAs)
A Pacific Institute for the Mathematical Sciences <a href="https://www.pims.math.ca/events/260817-pwoamla">Workshop</a>, held August 17-19 at the University of British Columbia.

What is Happening?
===

- **The Jacobian conjecture is false** (July 2026)
    - Claude Fable 5 + Lean

- **The Erdős unit distance conjecture is false** (May 2026)
    - OpenAI general-purpose reasoning model + mathematicians
    - (post-hoc) Aleph Prover/Lean formalization

- **The First Proof challenge** (early 2026)
    - Open problems (to avoid GPT looking up obscure papers)
    - Aletheia / Gemini 3 Deep Think architecture (no Lean)
    - Ensemble of Gemini models

<div class='fn'>
<a href="https://x.com/alpoge/status/2079028340955197566">L. Alpöge</a>.
<a href="https://openai.com/index/model-disproves-discrete-geometry-conjecture/">Erdös Unit</a>.
<a href="https://deepmind.google/blog/accelerating-mathematical-and-scientific-discovery-with-gemini-deep-think/">Deep Think</a>.
</class>

Math and AI
===

**LLMs + Proof Assistants**
  - _Generation_ by an LLM
  - _Verification_ by Lean, Experts, or Another LLM

<img src='img/brain.jpg' class='img-up-right' width=40%></img>

**AI as a learning tool***
- The combination of LLMs and Lean, even without<br/>integration, could make
advanced mathematics<br/> more accessible than ever.
- Use wisely : [AI in Papers](https://ai-math.zulipchat.com/#narrow/channel/539992-Web-public-channel---AI-Math/topic/Best.20practices.20for.20incorporating.20AI.20etc.2E.20in.20papers/near/546518354), [AI Generated Papers](https://categorytheory.zulipchat.com/#narrow/channel/229111-community.3A-general/topic/AI-generated.20papers/near/546399334)

AI Companies
- [DeepMind / AlphaProof](https://deepmind.google/blog/ai-solves-imo-problems-at-silver-medal-level/)
- [Aristotle] (https://aristotle.harmonic.fun/)
- [Axiom](https://axiommath.ai/)
- [Math, Inc](https://www.math.inc/)
...

Proof Assistants
===

- LLMs are better than most programmers at coding

- The Curry-Howard Isomorphism: math *is* coding

- Type Theory is the _lingua franca_ of formal math
    - The software and tooling has improved considerably
    - Implementation tradeoffs in CIC optimized
    - Improved modularity
    - Multiple options: L∃∀N, Rocq, Agda, ...

- Major projects
    - [Mathlib](https://github.com/leanprover-community/mathlib4), [CSLib](https://www.cslib.io/), [SciLean](https://github.com/lecopivo/SciLean)
    - [LeanPool](https://github.com/Vilin97/lean-pool)
    - [The Liquid Tensor Experiment](https://leanprover-community.github.io/blog/posts/lte-final/)
    - [Tao's Analysis](https://github.com/teorth/analysis)

<div class="fn">I find it absolutely insane that interactive proof assistants are now at the level
that, within a very reasonable time span, they can formally verify difficult original research.
— Peter Scholze</fn>





Mathlib
===

The Mathlib project and others have formalized even more.

<div><small><pre>
> ls Mathlib
Algebra                 Data                    LinearAlgebra           RingTheory
AlgebraicGeometry       Deprecated              Logic                   SetTheory
AlgebraicTopology       Dynamics                Mathport                Std
Analysis                FieldTheory             MeasureTheory           Tactic
CategoryTheory          Geometry                ModelTheory             Tactic.lean
Combinatorics           GroupTheory             NumberTheory            Testing
Computability           InformationTheory       Order                   Topology
Condensed               Init.lean               Probability             Util
Control                 Lean                    RepresentationTheory

> find Mathlib -name '*.lean' -print0 | xargs -0 wc -l | tail -1
  953293 total
</pre>
</small></div>

Seems like a lot, but _Web of Knowledge_ lists a total of 1,342,406 mathematics papers since 1900.

<div class='fn'>
https://github.com/leanprover-community/mathlib4<br>
https://strathmaths.wordpress.com/2013/04/17/how-much-mathematics-is-there
</div>

<div class="fn">Was 615506 in Jan 2026 when I last checked</div>

Course Goals
===

- Understand Type Theory as a foundation of mathematics
- Represent and reason about mathematics formally using Lean
- Use LLMs in combination with Lean to vibe-prove
- Implement a basic autoformalization loop
- Be prepared to teach an Automated Mathematics course

Detailed Topics
===

The representation and manipulation of mathematical knowledge symbolically
  - Foundations of Mathematics
  - Automated reasoning
  - The L∃∀N proof assistant
  - Vibe Proving

Specific Topics
  - Type theory
  - The Curry-Howard Isomorphism
  - Basic Math : Logic, Sets, Algebra, Topology
  - Mathlib
  - Autoformalization







Classroom Etiquette
===

- Respect each other
- Ask questions
- Make space for others
- Don't spray beta


Slides
===

What you are seeing is compiled from Lean code using my own custom slide
environment called `Slider`. This tool is not ready for production, so it may
not work on every browser, etc. I use Chrome.

The slides are on the web at:
- [https://klavinslab.org/LeanPIMS26/](https://klavinslab.org/LeanPIMS26/)

The source code to the slides are at:
- [https://github.com/klavins/LeanPIMS26](https://github.com/klavins/LeanPIMS26)
- Clone this repo and following along in class
- Do `git update` *before* each class meeting

Resources
===

Lean
- <a href="https://lean-lang.org/theorem_proving_in_lean4/" target="other">
  Theorem Proving in Lean
  </a>
- <a href="https://lean-lang.org/functional_programming_in_lean/" target="other">
  Lean Programming Book
  </a>
- <a href="https://leanprover-community.github.io/lean4-metaprogramming-book/" target="other">
  Lean Metaprogramming
  </a>
- <a href="https://leanprover-community.github.io/mathematics_in_lean" target="other">
  Mathematics in Lean
  </a>
- <a href="https://loogle.lean-lang.org/" target="other">
 Loogle
 </a> — Google for Lean
- <a href="https://leanprover.zulipchat.com/" target="other">
  Zulip Chat
  </a> — Discussion groups

Supplementary Texts
- Morten Heine Sørensen, Pawel Urzyczyn.
**Lectures on the Curry-Howard Isomorphism**.
Elsevier. 1st Edition, Volume 149 - July 4, 2006.
- **Homotopy Type Theory: Univalent Foundations of Mathematics**.
The Univalent Foundations Program Institute for Advanced Study.
[https://homotopytypetheory.org/book/](https://homotopytypetheory.org/book/).

-/

/-
Acknowledgements
===

I would like to acknowledge the students who took my special topics course offered the in the
Winter of 2025 and again in the Winter of 2027  at the University of Washington.
We all learned Lean together.
Much of the material here was developed in response to their questions and ideas.
At first,
Each time I teach this course I start out a few weeks ahead,
and by the end of the course I am a few weeks behind.


-/


--hide
end LeanW26
--unhide
