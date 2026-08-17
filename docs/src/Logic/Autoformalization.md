
Autoformalization
===
In mathematics the art of proposing a question must be held of higher value than solving it.
George Cantor

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



YAAD : Yet Another Autoformalizer Designer
===

<img src="img/yaad-loop.png" width=80%></img>

YAAD is a pre-release plugin for VS Code out of the Klavins Lab that allows you to build graphical workflows with LLMs, Lean Evaluators, and various utility blocks. Here's an example.




Installing
===

1. Install `uv` (a Python Package manager)
- [https://docs.astral.sh/uv/](https://docs.astral.sh/uv/)

2. Install YAAD
- Download `yaad.vsix` -- URL written on whiteboard
- Do VS Code → View Extension → "..." → Install from VSIX

3. Start a project
- Do `yaad: New Network` from the command palette and pick a location
- Make a new folder in a Lean project and open it. It will contain your yaad projects.
- Choose a new name for the yaad project.
- The first time you do this, `yaad` will ask if you want a new `pyproject.toml`. You do.



Prompts
===

<ex /> Start by placing a new Formatter block. Then double click to open it. Change the name to `Problem`. Change the template parameter to `file` and click new. Call the file `problem`. Put in something like and save everything.

> Implement mergesort, proving it terminates. Then prove that mergesort always results in a sorted list. Put this result in a theorem. Do not use all of mathlib, just what you need from lists and tactics. Do not add comments.

> IMPORTANT: Output ONLY LEAN 4 Code. Your response will go directly to a Lean 4 evaluator that will not accept anything except pure Lean 4 code.
Do not enclose the code in markdown style tickmarks. Do not add explanations of your thinking.

Finally, right click the new block and click run to see the output of the block appear next to the wire.



Google AI Studio
===

<img src="img/yaad-tutorial-2.png" style="display: block; margin-left: auto; margin-right: auto;" width=40%></img>

<ex /> Google AI Studio has a [API](https://aistudio.google.com/) with a free tier.
Go there and make a new API key.

Next:
- Make a `Gemini` block in YAAD and name it `Student`
- Change the extension to `.lean`
- Connect the output of your `Problem` block to the `body` input of the `Gemini` block.
- Right click the `Gemini` block to run it. It will complain that you don't have an API key, so enter one and try again.
- Inspect the output to see how well it does.





Lean
===

<img src="img/yaad-tutorial-3.png" style="display: block; margin-left: auto; margin-right: auto;" width=50%></img>

<ex /> Next place a Lean block and connect the output of<br/>
of the Student Block to its input.

Run the new block and check its output.




Make a Summarizer
===

<ex/> Create a new Formatter block called `Summarizer` with the template:

```none
No comments. No thought process. Below is their code and the errors it
produced. Provide an explanation of what they are doing wrong and
include ONLY the exact error messages relevant to your explanation.
Your goal is to help the student get it right the next time.

If there are no errors listed, just respond with "Nice Job!".

START PROBLEM
{problem}
END PROBLEM

START CODE (use the next line as line 1 when interpreting errors)
{code}
END CODE

ERRORS
{errors}
END ERRORS
```

Connect Summarizer to another Gemini Block
===

<img src="img/yaad-tutorial-3.png" style="display: block; margin-left: auto; margin-right: auto;" width=50%></img>

<ex /> Connect the Grader to the Summarizer and the Summarizer to another Gemini Block. Run to see the output.

<ex /> Continue to build the network until it looks like the closed-loop diagram a few slides ago. In that diagram:
- The `Remaining` block is a Formatter with the template
```none
{errors}{sorries}
```
- The circle is a stop block.
- The `Combiner` is a Formatter that combines the user's code with the `Teacher`'s response so it can be sent back to the `Student`. You will need to write a template for it.



Exercises
===

<ex /> Try some harder problems and don't use the `prelude` restriction.

<ex /> Other architectures you can explore include

- Having an LLM produce a plain english plan for how to prove whatever you are proving.
- Having the LLM output a proof with sorries that subsequent LLMs fill in.
- Using a swarm of `Consortium` block to make a swarm of LMs competing to formalize your statements.


```lean
--hide
end LeanW26
--unhide
```

License
===

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.  

Please see the full license at
<a href="https://github.com/klavins/LeanPIMS26">
https://github.com/klavins/LeanPIMS26
</a>

