
Polytopes --Luz Elena Grisales Gómez
===


Overview
===

One can represent polytopes in two ways:

- As the convex hull of finitely many points. In this case, we refer to it as a **V-polytope**.

- As the bounded intersection of finitely many closed halfspaces. In this case, we refer to it as an **H-polytope**.

<div style="display:flex; justify-content:center; align-items:center; gap:60px;">
  <img src='img/VPolytope.png' class='img-down-left' width=40%></img>
  <img src='img/HPolytope.png' class='img-down-right' width=30%></img>
</div>

Minkowski-Weyl Theorem
===

These two representations are equivalent due to the **Minkowski-Weyl Theorem**.

This is an unfinished formalization project for the Minkowski-Weyl Theorem.

In these slides we show to formaly define V-Polytopes, H-Polytopes, and Duality in Lean. We also formalize proofs of boundeness, closedness, and compactness results, and show how to state complex theorems in Lean.

**Repository:** https://github.com/luzelenag123/EE598_Final_Project



Set up
===
We'll need to perform pointwise operations and use noncomputable constructions (e.g. axiom of choice). For this, we will use:

```lean
-- using `scoped` below imports only the notation.
open scoped Pointwise
noncomputable section
```

We'll also need to define the space in which our polytopes will live:

```lean
variable {E : Type*}
  [NormedAddCommGroup E][InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E][DecidableEq E]
```

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

 Next, we'll add a few definitions directly associated to a VPolytope. For this, we create a namespace.

```lean
namespace VPolytope
```

Namespace
===
The `carrier` is going to produce the underlying set associated to the `VPolytope` structure. 
```lean
def carrier (P : VPolytope E) : Set E :=
  convexHull ℝ (P.points : Set E)
```
The `translate` map is going to produce a new `VPolytope` resulting from translating `P` by the vector `v`. 
```lean
def translate (P : VPolytope E) (v : E) : VPolytope E :=
  ⟨v +ᵥ P.points⟩
```

The definitions and theorems written inside this namespace can be accessed from outside the namespace by writting `VPolytope.{definition\theorem}`.


isCompact, isConvex
===
We can write simple theorems like the following inside this namespace.

```lean
theorem isCompact (P : VPolytope E) : IsCompact P.carrier := by
  simpa [carrier] using
    (P.points.finite_toSet).isCompact_convexHull
      (𝕜 := ℝ)
      (s := (P.points : Set E))

theorem isConvex (P : VPolytope E) : Convex ℝ P.carrier := by
  simpa [VPolytope.carrier] using
          (convex_convexHull ℝ (P.points : Set E))

end VPolytope
```

Exercise
===
Search Mathlib's `Compact.lean` file for theorems that help prove `isClosed` and `isBounded` in just one line.
Write your solutions inside the `VPolytope` namespace.

```lean
theorem isBounded (P : VPolytope E) : Bornology.IsBounded P.carrier := by
  sorry

theorem isClosed (P : VPolytope E) : IsClosed P.carrier := by
  sorry
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

This aligns with the mathematical definition of a halfspace depending only on a normal vector and an offset.


Namespace
===
Inside the Halfspace namespace we can define the carrier to be:

```lean
namespace Halfspace

def carrier (h : Halfspace E) : Set (E) :=
  {x | inner ℝ h.normal x ≤ h.offset}
```
 We can also prove that a Halfspace is `isClosed` as follows:
```lean
theorem isClosed (H : Halfspace E) : IsClosed H.carrier := by
  dsimp [carrier]
  apply isClosed_le
  · exact Continuous.inner continuous_const continuous_id
  · exact continuous_const
```

DecidableEq
===
`DecidableEq` is a typeclass in Lean. To tell Lean that the `Halfspace` type has decidable equality, we need to instantiate this typeclass.

Lean can sometimes infer the instance using the tactic `infer_instance`:

```lean
instance [DecidableEq E] : DecidableEq (Halfspace E) := by
  classical
  infer_instance
```
 We need `DecidableEq` in order to be able to create sets of halfspaces.
```lean
end Halfspace
```

Exercise
===
Use the help of AI to generate a proof for `isConvex`.
```lean
theorem isConvex (H : Halfspace E) : Convex ℝ H.carrier := by
  sorry
```


H-Polyhedra
===

An **H-Polyhedron** is a finite intersection of halfspaces. An **H-Polytope** is an H-Polyhedron that is also bounded. In Lean, we can encode this as follows:

```lean
structure HPolyhedron (E : Type*)
  [DecidableEq E][NormedAddCommGroup E]
  [InnerProductSpace ℝ E][FiniteDimensional ℝ E]
where
  (halfspaces : Finset (Halfspace E))

namespace HPolyhedron

def carrier (P : HPolyhedron E) : Set E :=
  ⋂ h ∈ P.halfspaces, (h.carrier)

end HPolyhedron
```

H-Polytopes
===
Since an H-Polytope is an H-Polyhedron with additional conditions, we can use `extends` in Lean.

```lean
structure HPolytope (E : Type*)
  [DecidableEq E][NormedAddCommGroup E]
  [InnerProductSpace ℝ E][FiniteDimensional ℝ E]
extends HPolyhedron E where
  (bounded : Bornology.IsBounded (toHPolyhedron.carrier))
```

We are extending the `HPolyhedron` definition by adding the condiiton that it must be `bounded`.

If defined like this, an `HPolytope` will inherit definitions and theorems defined for an `HPolyhedron`.


Exercise
===

```lean
abbrev ℝn (n : ℕ) := EuclideanSpace ℝ (Fin n)
```

Define `P` as the `VPolytope` generated by (0,0), (0,1), and (1,0). Define `Q` as the `HPolyhedron` generated by the equations x ≥ 0, y ≥ 0, and x + y ≤ 1.

```lean
def P : VPolytope (ℝn 2) := sorry
def Q : VPolytope (ℝn 2) := sorry
```

**Extra Challenge:** Define how to translate an `HPolyhedron` inside its namespace.

```lean
def translate (P : HPolyhedron E) (v : E) : HPolyhedron E :=
  sorry
```


Duality
===
A key tool in prove the Minkowski-Weyl Theorem is duality.

Some version of duality is already implemented in Mathlib, but it is too general and difficult to parse for our purposes, so we implement our own:

```lean
def dual (P : Set E) : Set E :=
  ⋂ x ∈ (P \ {0}), (Halfspace.mk x 1).carrier
```

One can observe that duality sends points to halfspaces.


The dual of a VPolytope
===
One can guess directly from the definition of duality that the dual of a VPolytope is an HPolyhedron since points become halfspaces.

Therefore, we can define the dual of a `VPolytope` as:

```lean
def VPolytope.dual (P : VPolytope E) : HPolyhedron E :=
  { halfspaces := P.points.image (fun x => Halfspace.mk x 1) }
```

A natural theorem would then be:

```lean
theorem dual_of_VPolytope (P : VPolytope E) : dual P.carrier = P.dual.carrier := sorry
```

This is a long Lean proof, so we are not doing it today. If you want, you can try to generate a proof using AI.


Exercise
===
Prove the following basic properties of duality.

```lean
namespace dual

theorem zero_mem (P : Set E) : (0 : E) ∈ dual P := by
  sorry

theorem isAntitone {A B : Set E} (h : A ⊆ B) : dual B ⊆ dual A := by
  sorry

end dual
```

It is also true that the dual of a set of is closed and convex, and should follow directly from the Halfspace properties.


Main theorems
===
Some of the main theorems we want to prove in order to establish the equivalence between VPolytopes and HPolytope include:

```lean
theorem separation_compact_closed
    {C D : Set E}
    (hC_nonempty : C.Nonempty)
    (hC_convex : Convex ℝ C) (hC_compact : IsCompact C)
    (hD_nonempty : D.Nonempty)
    (hD_convex : Convex ℝ D) (hD_closed : IsClosed D)
    (hdisj : Disjoint C D) :
    ∃ (a : E) (b : ℝ),
      a ≠ 0 ∧
      C ⊆ {x | inner ℝ a x < b} ∧
      D ⊆ {x | inner ℝ a x > b} := by
  --brief
  obtain ⟨f, u, v, hCsep, huv, hDsep⟩ :=
    geometric_hahn_banach_compact_closed hC_convex hC_compact hD_convex hD_closed hdisj
  --
  -- Convert the functional f into inner-product form:
  -- f x = inner a x for some vector a (Riesz representation).
  -- (Keep as sorry until exact lemma name is confirmed in your Mathlib version.)
  obtain ⟨a, ha⟩ : ∃ a : E, ∀ x : E, f x = inner ℝ a x := by
    -- The map toDualMap is surjective for complete spaces (EuclideanSpace is complete).
    -- So there exists `a` such that `f = toDualMap ℝ (ℝn n) a`.
    have hsurj : Function.Surjective (InnerProductSpace.toDualMap ℝ E) :=
      LinearIsometryEquiv.surjective (InnerProductSpace.toDual ℝ E)
    obtain ⟨a, rfl⟩ := hsurj f
    use a
    intro x
    -- Now show: (toDualMap ℝ (ℝn n) a) x = inner ℝ a x
    exact InnerProductSpace.toDualMap_apply_apply ℝ
  --
  -- Choose b as midpoint between u and v.
  refine ⟨a, (u + v) / 2, ?_, ?_, ?_⟩
  --
  · -- Prove a ≠ 0.
    intro ha0
    -- Pick one point c in C and one point d in D.
    rcases hC_nonempty with ⟨c, hc⟩
    rcases hD_nonempty with ⟨d, hd⟩
    -- If a=0, then f is identically 0 (via f x = inner a x).
    have hfc : f c = 0 := by simpa [ha0] using ha c
    have hfd : f d = 0 := by simpa [ha0] using ha d
    -- From C-side strict inequality: f c < u, so 0 < u.
    have h1 : 0 < u := by
      have := hCsep c hc
      simpa [hfc] using this
    -- From D-side strict inequality: v < f d, so v < 0.
    have h2 : v < 0 := by
      have := hDsep d hd
      simpa [hfd] using this
    -- Contradiction with u < v.
    linarith [huv, h1, h2]
  --
  · -- Show C ⊆ {x | inner a x < (u+v)/2}.
    intro x hx
    -- From Hahn–Banach: f x < u for x∈C.
    have hx' : f x < u := hCsep x hx
    -- Midpoint is strictly above u because u < v.
    have hm : u < (u + v) / 2 := by linarith [huv]
    -- Therefore f x < midpoint.
    have : f x < (u + v) / 2 := lt_trans hx' hm
    -- Rewrite f x as inner a x.
    simpa [ha x] using this
  --
  · -- Show D ⊆ {x | inner a x > (u+v)/2}.
    intro x hx
    -- From Hahn–Banach: v < f x for x∈D.
    have hx' : v < f x := hDsep x hx
    -- Midpoint is strictly below v because u < v.
    have hm : (u + v) / 2 < v := by linarith [huv]
    -- Therefore midpoint < f x.
    have : (u + v) / 2 < f x := lt_trans hm hx'
    -- Rewrite f x as inner a x.
    simpa [ha x] using this
  --unbrief
```

More main theorems
===

```lean
theorem dual_of_dual
  (X : Set E) :
  dual (dual X)
  = closure
    (convexHull ℝ
    (Set.union X ({0} : Set E))) := sorry

theorem HPolytope_is_VPolytope :
  ∀ P : HPolytope E,
  ∃ Q : VPolytope E, P.carrier = Q.carrier := sorry

theorem VPolytope_is_HPolytope [Nontrivial E] :
  ∀ P : VPolytope E,
  ∃ Q : HPolytope E, P.carrier = Q.carrier := sorry

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

