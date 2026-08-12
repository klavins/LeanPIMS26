--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.

import Mathlib

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.flexible false

namespace LeanW26


/-
Autoformalization
===
In mathematics the art of proposing a question must be held of higher value than solving it.
George Cantor

Under Construction
===

This deck is still under construction. Check back later.

Agents vs Workflows
===

From Anthropic's [Building effective agents](https://www.anthropic.com/engineering/building-effective-agents):

- **Workflows** are systems where LLMs and tools are orchestrated through predefined code paths.

    - Most mathematics autoformalizers
    - Some aspects of Claude Code (e.g. slash commands)

- **Agents** are systems where LLMs dynamically direct their own processes and tool usage, maintaining control over how they accomplish tasks.

    - Claude code main loop
    - Arbitrary coding tasks
    - Tools: `read`, `write`, `edit`, `bash`, `web search`, `spawn sub-agents`

- **Thinking** in Claude and similar is (probably) a combination.

    - Switch roles as an evaluator and ptimizer with a shared document
    - If tools are involved, run them like an agent and incorporate the results for the evaluator

Examples
===

- OpenAI's recent [10 problems](https://openai.com/index/ten-advances-in-mathematics/) is described as a fairly simple workflow with their latest model, Astra:

    - Problem → [LLM] → Informal Sketch → [ LLM ⇄ Lean ] → Result

- OpenAI's [Erdös unit distance conjecture disproof](https://openai.com/index/model-disproves-discrete-geometry-conjecture/):

    - problem → internal model → [ human ⇄ Codex ] → Lean certification
    - First attempt without Lean certs was found to be incorrect

- Levent Alpöge states the [Jacobian conjecture](https://www.sciencedaily.com/releases/2026/08/260804034634.htm) counterexample was just Claude + Fable _chat_ in a browser → Wolfram Alpah to check the result. So this is not technically autoformalization since it was human assisted.

Noe of these examples involved models explicitly trained on math, as some of the Math-AI startups are doing (e.g. Aristotle).

Older Examples
===

| system | structure |
| --- | --- |
| [GPT-f](https://arxiv.org/abs/2009.03393) (2020) | transformer + proof search over Metamath |
| [HyperTree Proof Search](https://arxiv.org/abs/2205.11491) (2022) | AlphaZero-style search with online training |
| [LeanDojo / ReProver](https://arxiv.org/abs/2306.15626) (2023) | retrieval-augmented tactic generation in a fixed loop |
| [AlphaProof](https://www.nature.com/articles/s41586-025-09833-y) (Nature, 2025) | RL over a formal search |
| [DeepSeek-Prover-V2](https://arxiv.org/abs/2504.21801) (2025) | RL for recursive subgoal decomposition |

-/

--hide
end LeanW26
--unhide
