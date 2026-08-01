
Breaking Lean
===

Lean's definitional equality and impredicative `Prop` make Lean's type theory
_not_ strongly normalizing. Here we present the Abel–Coquand-style construction
 of a non-normalizing closed term.

<div class='fn'>Andreas Abel ; Thierry Coquand, <a href="https://lmcs.episciences.org/6606">https://lmcs.episciences.org/6606</a></div>


```lean
--hide
set_option linter.defProp false
--unhide
```
 In the simply typed lambda calculus, you cannot write `λ x => x x`. 
```lean
#check_failure (fun x => x x)                    -- δ is not definable
#check_failure (fun x => x x) (fun x => x x)     -- neither is Ω
```


However,
we can write a version of this using Lean's `Prop`.

To proceed, we want to build a type for Ω. It should be something like this:

```lean
def T : Type u := ∀ (X : Type u), X → X
```

But this is a universe error: `∀ X : Type u, X → X` lives in `Type (u+1)`,
one level above the `X` it quantifies over.

Building Ω
===

A quantification over all propositions is itself a proposition.


```lean
def T : Prop := ∀ (p : Prop), p → p
```
 Now we define `δ`, which plays the role of `λ x => x x`. 
```lean
def δ : T → T := fun (z : T) => (z (T → T) id) z
```
 Then define `δ'` as `δ` in disguise.

```lean
def δ' : T := fun p a =>
  cast (propext (iff_of_true id a) : (T → T) = p) δ
```


Since `T → T` and `p` are both true (witnessed by `id` and `a`), `propext`
makes them *equal*, and `cast` re-types `δ` as a proof of `p`.

Now we define Ω.
```lean
def Ω : T := δ δ'
```

Accessibility
===

Accessibility is defined inductively and is used the definition of a well-founded relation.

```lean
inductive Acc {α : Sort u} (r : α → α → Prop) : α → Prop where
  | intro (x : α) (h : (y : α) → r y x → Acc r y) : Acc r x
```

In particular, consider the relation on ℕ containing no pairs.


```lean
def r : Nat → Nat → Prop := fun _ _ => False
```


Trivially, every number is accessible via this relation.
Using `Acc` we define two elements of `Acc r 0`. The first is trivial:


```lean
def acc0 : Acc r 0 := Acc.intro 0 (fun _ h => False.elim h)
```

Looping rfl
===

Here is another proof that `0` is accessibleusing `Ω` 
```lean
def accLoop : Acc r 0 := Ω (Acc r 0) acc0
```
 Since both are proofs of `Acc r 0`, by proof irrelevance they are the same.  
```lean
example : accLoop = acc0 := rfl
```
 Now define `F` to be the natural number we get by matching accLoop,
ignoring arguments, and returning 0. 
```lean
noncomputable def F : Nat :=
  match accLoop with
  | Acc.intro _ _ => 0
```
 Then attempting to show that `F = 0` will loop forever (or until Lean gives up).

```lean
example : F = 0 := rfl -- maximum recursion depth has been reached
```


License
===

Copyright (C) 2025  Eric Klavins

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.   

