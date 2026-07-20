
Polytopes --Luz Elena Grisales Gómez
===


Overview
===

One can represent polytopes in two ways:

- As the convex hull of finitely many points. In this case, we refer to it as a *V-polytope*.

- As the bounded intersection of finitely many closed halfspaces. In this case, we refer to it as an *H-polytope*.

These two representations are equivalent due to the *Minkowski-Weyl Theorem*.



Set up
===
For some of the definitions included here, we'll need for perform pointwise operations and use noncomputable constructions (e.g. choice). For this, we will use:

```lean
open scoped Pointwise -- using `scoped` imports only the notation.
noncomputable section
```

We'll also need to define the space in which our polytopes will live:

```lean
variable {E : Type*}
[DecidableEq E] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
```

This creates a finite-dimensional vector space equipped with a real inner-product and with decidable equality.


V-Polytopes
===
We can define V-Polytopes as a structure storing its set of generating points.

```lean
structure VPolytope (E : Type*)
  [DecidableEq E]
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
where
  points : Finset E
```

Now we can add a few definitions directly associated to a V-polytope:

```lean
namespace VPolytope
```
- Underlying set associated to the `VPolytope` structure. 
```lean
def carrier (P : VPolytope E) : Set E :=
  convexHull ℝ (↑P.points : Set E)
```
- VPolytope resulting from translating `P` by vector `v`. 
```lean
def translate (P : VPolytope E) (v : E) : VPolytope E :=
  ⟨v +ᵥ P.points⟩
```


Proving isBounded, isConvex, isClosed
===

```lean
theorem isCompact (P : VPolytope E) : IsCompact P.carrier := by
  simpa [carrier] using
      (Set.Finite.isCompact_convexHull
        (s := (↑P.points : Set E))
        (P.points.finite_toSet))

theorem isClosed (P : VPolytope E) : IsClosed P.carrier := by
  exact (isCompact P).isClosed

theorem isBounded (P : VPolytope E) : Bornology.IsBounded P.carrier := by
  exact (isCompact P).isBounded

theorem isConvex (P : VPolytope E) : Convex ℝ P.carrier := by
  simpa [VPolytope.carrier] using
          (convex_convexHull ℝ (↑P.points : Set E))

end VPolytope
```


Halfspaces
===
We can naturally define a halfspace as follows:

```lean
structure Halfspace (E : Type*)
  [DecidableEq E]
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
where
  normal : E
  offset : ℝ
```

Inside the Halfspace namespace we can define the carrier to be:

```lean
namespace Halfspace

def carrier (h : Halfspace E) : Set (E) :=
  {x | inner ℝ h.normal x ≤ h.offset}

-- Exercise: Prove `isConvex` and `isClosed`. You might need to find/use some basic mathlib results.
theorem isClosed (H : Halfspace E) : IsClosed H.carrier := by
  sorry
theorem isConvex (H : Halfspace E) : Convex ℝ H.carrier := by
  sorry
```

Lean can infer how to decide equality between two halfspaces:

```lean
instance [DecidableEq E] : DecidableEq (Halfspace E) := by
  classical
  infer_instance
```
 We need to instanciate this typeclass in order to be able to create sets of halfspaces.
```lean
end Halfspace
```


H-Polytopes
===

An *H-Polyhedron* is a finite intersection of halfspaces. An *H-Polytope* is an *H-Polyhedron* that is also bounded. In Lean, we can encode this as follows:

```lean
structure HPolyhedron (E : Type*)
  [DecidableEq E]
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
where
  (halfspaces : Finset (Halfspace E))

namespace HPolyhedron

def carrier (P : HPolyhedron E) : Set E :=
  ⋂ h ∈ P.halfspaces, (h.carrier)

-- We can also include theorems like `isConvex` and `isClosed` inside this namespace.

-- Challenge: Define how to translate an HPolyhedron.
def translate (P : HPolyhedron E) (v : E) : HPolyhedron E :=
  sorry

end HPolyhedron

structure HPolytope (E : Type*)
  [DecidableEq E]
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
extends HPolyhedron E where
  (bounded : Bornology.IsBounded (toHPolyhedron.carrier))
```

An `HPolytope` will inherit definitions and theorems defined for an `HPolyhedron`.


Duality
===
A key tool in prove the Minkowski-Weyl Theorem is duality.

Some version of duality is already implemented in Mathlib, but it is too general and difficult to parse for our purposes, so we implement our own:

```lean
def dual (P : Set E) : Set E :=
  ⋂ x ∈ (P \ {0}), (Halfspace.mk x 1).carrier
```

Exercise: With this definition we can now prove some basic properties of duality.

```lean
namespace dual

theorem isClosed (P : Set E) : IsClosed (dual P) := by
  sorry
theorem isConvex (P : Set E) : Convex ℝ (dual P) := by
  sorry
theorem zero_mem (P : Set E) : (0 : E) ∈ dual P := by
  sorry
theorem isAntitone {A B : Set E} (h : A ⊆ B) : dual B ⊆ dual A := by
  sorry

end dual
```

We can also define what the `HPolytope` that is dual to a `VPolytope` should be:

```lean
def VPolytope.dual (P : VPolytope E) : HPolyhedron E :=
  { halfspaces := P.points.image (fun x => Halfspace.mk x 1) }
```

A natural theorem would then be:

```lean
theorem dual_of_VPolytope (P : VPolytope E) : dual P.carrier = P.dual.carrier := sorry
```

This is a long Lean proof, so we are not doing it today.


Main Theorems
===
Some of the main theorems we want to prove in order to establish the equivalence between VPolytopes and HPolytope include:

```lean
theorem separation_compact_closed
    {C D : Set E}
    (hC_nonempty : C.Nonempty)
    (hC_convex : Convex ℝ C)
    (hC_compact : IsCompact C)
    (hD_nonempty : D.Nonempty)
    (hD_convex : Convex ℝ D)
    (hD_closed : IsClosed D)
    (hdisj : Disjoint C D) :
    ∃ (a : E) (b : ℝ),
      a ≠ 0 ∧
      C ⊆ {x | inner ℝ a x < b} ∧
      D ⊆ {x | inner ℝ a x > b} := sorry

theorem dual_of_dual
  (X : Set E) :
  dual (dual X)
    = closure (convexHull ℝ (Set.union X ({0} : Set E))) := sorry

theorem HPolytope_is_VPolytope : ∀ P : HPolytope E, ∃ Q : VPolytope E, P.carrier = Q.carrier := sorry

theorem VPolytope_is_HPolytope [Nontrivial E] : ∀ P : VPolytope E, ∃ Q : HPolytope E, P.carrier = Q.carrier := sorry

--hide
end
end LeanW26
--unhide
```

License
===

Copyright (C) 2025  Eric Klavins

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.   

