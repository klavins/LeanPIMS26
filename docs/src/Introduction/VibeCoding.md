
Vibe Proving
===
Mathematics is the cheapest science. Unlike physics or chemistry, it does not require any expensive equipment. All one needs for mathematics is a pencil and paper (George Pólya)†
†You will also need a Claude Code account and a reasonably powerful laptop.


Claude Code
===

Claude code runs locally on your computer.
- It can read and write files of pretty much any type.
- It can interact with Lean directly using the Lean LSP
- It can spawn agents to work on specific tasks (e.g. code reviews, refactors)
- It can search the web and download content

Tools
- A tool is an executable capability that lives outside Claude Code.
- For example: Bash (and everything you can invoke from Bash), Read, Edit, WebSearch, or tools for talking to Lean

Skills
- A skill is a set of packaged instructions that load into the LLM context
— For example: markdown playbooks that activate when you invoke them or when their trigger conditions match.

<div class='fn'>Other similar agentic coding tools include Cursor, Github CoPilot, and OpenAI Codex.</div>

What is the Lean LSP?
===

- The **Lean Language Server Protocol** is Lean 4's built-in language server — the same process that powers VS Code's Lean experience.

- It compiles your file incrementally and serves structured queries over the Language Server Protocol: diagnostics (errors/warnings), proof goals at a cursor position, hover types and docs, completions, and go-to-definition. Everything the InfoView shows you comes through it.

- Claude talks to it through an MCP server [lean-lsp-mcp](https://github.com/oOo0oOo/lean-lsp-mcp) that wraps the language server and exposes its queries as tools Claude can use.

- Python interface: [leanclient](https://github.com/oOo0oOo/leanclient)

- Documentation [here](https://github.com/leanprover/lean4/blob/master/src/Lean/Server/README.md)


Installing
===

- [Claude Code](https://claude.com/product/claude-code) -- just follow the instructions

- Installing Lean MCP

```bash
curl -LsSf https://astral.sh/uv/install.sh | sh     # or: brew install uv`
claude mcp add --scope user lean-lsp -- uvx lean-lsp-mcp
```

- Installing Lean Skills
```bash
claude plugin marketplace add cameronfreer/lean4-skills
claude plugin install lean4@lean4-skills
```

- Running
```bash
claude
```

- Adjusting effort
```none
/model
```

Demo 1: Helping with Proofs
===

Navigate to `Maths/Algebra.lean` line 876 where it says

```lean
theorem one_inv : (one:F)⁻¹ = one := sorry
```

Then prompt with

> In LeanPIMS26/Maths/Algebra.lean, do the proof of the exercise on line 876.

which gives

```lean
theorem one_inv : (one:F)⁻¹ = one := by
  have h : (one:F) * one⁻¹ = one := mul_inv_prop one_ne_e
  rw[mul_id_left] at h
  exact h
```

Claude writes to the file, checks the LSP for errors, iterates until the proof typechecks, and provides a summary (not shown).


Demo 2: Autoformalizing
===

I entered the prompt:

> Create the file LeanPIMS26/Introduction/cc-demo.lean. In that file, implement mergesort, proving it terminates. Run #eval on a few examples of different types of lists. Then prove that mergesort always results in a sorted list. Put this result in a theorem. The proofs to any theorems should be less than 20 lines long, so you may need to define lemmas that work out intermediate results. Do not use all of mathlib, just what you need from lists and tactics. Iterate on the file using the LSP until there are no errors remaining. Do not add comments.

I waited for 7m, 14s and got 99 lines of code with the ultimate theorem:

```lean
theorem msort_sorted (htot : ∀ a b : α, a ≤ b ∨ b ≤ a)
  : ∀ l : List α, Sorted (msort l)
```

The file contains no imports. Claude reinvented total orders and the `Sorted` predicate.

Refining
===

Fixing some issues:

> A few issues to fix: There should be a mathlib class for a total order, so use that. Don't separate out variable definitions. Rather, add them to the defs and theorems you state so they are clear from reading them. And always use " := by" for theorems instead of jumping right in. Finally, do a pass through the file as though you were Leo DeMoura himself checking for proper idiomatic use of Lean4.

Which produced

```lean
theorem sorted_mergeSort {α : Type*} [LinearOrder α] (l : List α) : Sorted (mergeSort l) := by
  fun_induction mergeSort l with
  | case1 => exact .nil
  | case2 a => exact .cons True.intro .nil
  | case3 a b rest ih₁ ih₂ => exact sorted_merge ih₁ ih₂
```


Issues
===

It is super important to look at the definitions. In this case, `Sorted` is correct, but the name `LowerBound` is very misleading. It should probably be called `LeHead` since it just checks that a is `≤` the head of a list.

```lean
def LowerBound {α : Type*} [LE α] (a : α) : List α → Prop
  | [] => True
  | b :: _ => a ≤ b

inductive Sorted {α : Type*} [LE α] : List α → Prop where
  | nil : Sorted []
  | cons {a : α} {l : List α} : LowerBound a l → Sorted l → Sorted (a :: l)
```

I prompted _just write Sorted directly without using the helper_ and it produced

```lean
inductive Sorted {α : Type*} [LE α] : List α → Prop where
  | nil : Sorted []
  | single (a : α) : Sorted [a]
  | cons {a b : α} {l : List α} : a ≤ b → Sorted (b :: l) → Sorted (a :: b :: l)
```

Demo 3 : Plan Mode
===

I entered the prompt:

> Consider the quotient topology on two copies of ℝ in which all _but_ the zeros are identified with their corresponding elements. Instiante this space using Mathlib's TopologicalSpace and show that the resulting space is not Hausdorff. Before jumping it, go into plan mode to make sure that you have all the steps needed to be successful. Then present me with the plan. When we are ready to write the code, put it in LeanPIMS26/Sandbox/TwoCopies.lean.

Then I asked it to implement the plan in **auto** mode.

Refinements
===

Then I looked at the file and asked:

> Do a complete review on the resulting file, and code-golf the whole thing. Make sure no proofs are overly long (roughly 10 lines max) and break out lemmas and simps if necessary. Finally, take out all the comments. This is not intended to be used as course notes.

It responded:
1. The mathematical content is really just "ℝ has no isolated points," which Mathlib expresses as the punctured neighborhood filter `𝓝[≠] 0` being `NeBot`. I extracted that as a 3-line helper.
2. `o₁_ne_o₂` stays a one-liner but now dispatches the extra Or branch of the new relation with `Sum.inl_ne_inr`.


Demo 4: A Substantial Request
===


>  Now come up with a plan to show that the fundamental group of `TwoOrigins` is the integers under addition.

It thought for 10 minutes, looked into what it could use from Mathlib, and gave me a four phase plan:

1.  Mathlib does not have `π₁(S¹) ≅ ℤ`, and has no Seifert–van Kampen. But Junyan Xu's 2025 covering-space development provides the complete abstract theorem we need.

2.  So the entire project reduces to: build the `ℤ-cover E → TwoOrigins`, check the four structure fields, and prove `SimplyConnectedSpace E`. The last item is the only mathematically hard part.

3. Plan
    a.  Phase 1 — Cover.lean: E, the action, p (300–500 lines)
    b.  covering structure (200–400 lines, same file)
    c. SimplyConnectedSpace E (the hard core, 800–2000 lines)
    d. Phase 4 — assembly (50 lines, `TwoOriginsPi1.lean`)

Result
===

1366 lines across four Sandbox files.

Builds `ZigZag`, the universal cover: countably many real lines glued into an infinite zigzag (`ℝ × ℤ` quotiented by gluing line `n` to line `n+1` along alternating half-lines), with `ℤ` acting by shifting two lines.

Shows `IsAddQuotientCoveringMap p ℤ`.

Shows `SimplyConnectedSpace ZigZag`.

Mathlib's IsAddQuotientCoveringMap.fundamentalGroupEquiv (quotient covering + simply connected total space ⟹ π₁(base) ≅ deck group) plus removing the ᵐᵒᵖ.

The plan's reconnaissance confirmed Mathlib still has no π₁(S¹) ≅ ℤ — yet with the same two 2025 theorems it now follows in about three lines from AddCircle.isAddQuotientCoveringMap_coe (ℝ is simply connected). That's either a nice student project or a small Mathlib PR!


Exercises
===

<ex /> Repeat the demos here on subjects of your choosing. If you are new to Lean expect to over- or underestimate on your first few attempts.

<ex /> Ask Claude Code to do all the exercises in the LEANPIMS26 materials. Have it put the results somewhere like LEANPIMS26/Solutions. Don't look them though unless you get stuck!



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

