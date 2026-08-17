
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

In these slides we show how to formally define V-Polytopes, H-Polytopes, and Duality in Lean. We also formalize proofs of boundedness, closedness, and compactness results, and show how to state complex theorems in Lean.

**Repository:** https://github.com/luzelenag123/EE598_Final_Project

**These slides rely on several Mathlib libraries that we will be black-boxing**



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
  [FiniteDimensional ℝ E]
```

V-Polytopes
===
We can define V-Polytopes as a structure storing its set of generating points, together with a proof that this set is finite.

```lean
structure VPolytope (E : Type*)
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
where
  points : Set E
  finite : points.Finite
```

Mathlib also has a type `Finset α` of finite sets, which would let us drop the `finite` field. We do not use it here, and the reason is worth knowing.


Why `Set` and not `Finset`?
===
A `Finset` is a list of elements carrying a proof that it has *no duplicates*, so every operation has to maintain that invariant. Inserting an element means asking "is it already in there?", and *answering* that question requires a `DecidableEq α` instance.

But equality of points in a real inner product space is not decidable, so any instance we supplied would be classical: we would be paying for a computation we can never actually run.

With `Set`, duplicates are invisible from the start (`x = a ∨ x = a` is just `x = a`), and `Set.Finite` is a `Prop`, so it may be proved classically for free. The cost is that we carry the finiteness proof around by hand.


The VPolytope namespace
===
 Next, we'll add a few definitions directly associated to a VPolytope. For this, we create a namespace.

```lean
namespace VPolytope
```

The `carrier` is going to produce the underlying set associated to the `VPolytope` structure. 
```lean
def carrier (P : VPolytope E) : Set E :=
  convexHull ℝ P.points
```
The `translate` map is going to produce a new `VPolytope` resulting from translating `P` by the vector `v`. Note that we must also supply a proof that the translated set is still finite. Translations are not decoration: they are used in the proof of the Minkowski-Weyl theorem. 
```lean
def translate (P : VPolytope E) (v : E) : VPolytope E :=
  ⟨v +ᵥ P.points, P.finite.vadd_set⟩
```

The definitions and theorems written inside this namespace can be accessed from outside the namespace by writing `VPolytope.{definition/theorem}`.


isCompact, isConvex
===
We can write simple theorems like the following inside this namespace.

```lean
theorem isCompact (P : VPolytope E) : IsCompact P.carrier :=
  P.finite.isCompact_convexHull (𝕜 := ℝ)

theorem isConvex (P : VPolytope E) : Convex ℝ P.carrier :=
  convex_convexHull ℝ _
```

The `_` in the proof of `isConvex` can be replaced with `P.points`. However, Lean is able to infer the argument!

An underscore is simply an argument you decline to write: Lean recovers it from the surrounding types. Two more will turn up later in these slides, so keep an eye out.


Exercise 1: closed and bounded
===
You have already proved that the carrier is compact, and both of these follow from that in a single line. Explore what the `IsCompact.` namespace offers and reach for dot notation.
Write your solutions inside the `VPolytope` namespace.

```lean
theorem isBounded (P : VPolytope E) : Bornology.IsBounded P.carrier := by
  exact (P.isCompact).isBounded

theorem isClosed (P : VPolytope E) : IsClosed P.carrier := by
  exact (P.isCompact).isClosed

end VPolytope
```

Halfspaces
===
We can naturally define a halfspace as follows:

```lean
structure Halfspace (E : Type*)
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
where
  normal : E
  offset : ℝ
```

This aligns with the mathematical definition of a halfspace depending only on a normal vector and an offset.


The Halfspace namespace
===
Inside the Halfspace namespace we can define the carrier to be:

```lean
namespace Halfspace

def carrier (H : Halfspace E) : Set E :=
  {x | inner ℝ H.normal x ≤ H.offset}
```
 We can also prove that a Halfspace is `isClosed` as follows:
```lean
theorem isClosed (H : Halfspace E) : IsClosed H.carrier := by
  dsimp [carrier]
  apply isClosed_le
  · exact Continuous.inner continuous_const continuous_id
  · exact continuous_const
```

Exercise 2: convexity of a halfspace
===
Use the help of AI to generate a proof for `isConvex`.

```lean
theorem isConvex (H : Halfspace E) : Convex ℝ H.carrier := by
  dsimp [carrier]
  unfold Convex
  intros x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred] at hx hy ⊢
  calc inner ℝ H.normal (a • x + b • y)
      = a * inner ℝ H.normal x + b * inner ℝ H.normal y := by
        rw [inner_add_right, inner_smul_right, inner_smul_right]
    _ ≤ a * H.offset + b * H.offset := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hx ha
        · exact mul_le_mul_of_nonneg_left hy hb
    _ = (a + b) * H.offset := by ring
    _ = H.offset := by rw [hab]; ring

end Halfspace
```

H-Polyhedra
===

An **H-Polyhedron** is a finite intersection of halfspaces. An **H-Polytope** is an H-Polyhedron that is also bounded. In Lean, we can encode this as follows:

```lean
structure HPolyhedron (E : Type*)
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E][FiniteDimensional ℝ E]
where
  halfspaces : Set (Halfspace E)
  finite : halfspaces.Finite

namespace HPolyhedron

def carrier (P : HPolyhedron E) : Set E :=
  ⋂ h ∈ P.halfspaces, (h.carrier)

def translate (P : HPolyhedron E) (v : E) : HPolyhedron E :=
  {halfspaces := (fun h : Halfspace E =>
        { normal := h.normal,
          offset := h.offset + inner ℝ h.normal v
        }) '' P.halfspaces
   finite := P.finite.image _
  }

end HPolyhedron
```

H-Polytopes
===
Since an H-Polytope is an H-Polyhedron with additional conditions, we can use `extends` in Lean.

```lean
structure HPolytope (E : Type*)
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E][FiniteDimensional ℝ E]
extends HPolyhedron E where
  bounded : Bornology.IsBounded toHPolyhedron.carrier
```

We are extending the `HPolyhedron` definition by adding the condition that it must be `bounded`. Note that this reads the same way as the `finite` field above: an `HPolytope` is an `HPolyhedron` carrying one more proof.

If defined like this, an `HPolytope` will inherit definitions and theorems defined for an `HPolyhedron`.


Exercise 3: concrete polytopes
===

```lean
abbrev ℝn (n : ℕ) := EuclideanSpace ℝ (Fin n)
```

Define `P` as the `VPolytope` generated by (0,0), (0,1), and (1,0). Define `Q` as the `HPolyhedron` generated by the equations x ≥ 0, y ≥ 0, and x + y ≤ 1.

Remember that each one now needs a finiteness proof as well. The theorem `Set.toFinite _` will discharge it. There is the second underscore: what does it stand for here? It is the set itself, as the two answers below spell out.

```lean
-- (0,0), (0,1), (1,0)
def P : VPolytope (ℝn 2) :=
  VPolytope.mk
    { !₂[0, 0],
      !₂[1, 0],
      !₂[0, 1] }
    (Set.toFinite _) -- Or Set.toFinite ({!₂[0, 0],!₂[1, 0],!₂[0, 1]} : Set (ℝn 2))

-- In terms of halfspaces now
def h1 : Halfspace (ℝn 2) := ⟨ !₂[-1, 0], 0 ⟩  -- x ≥ 0
def h2 : Halfspace (ℝn 2) := ⟨ !₂[0, -1], 0 ⟩  -- y ≥ 0
def h3 : Halfspace (ℝn 2) := ⟨ !₂[1, 1], 1 ⟩   -- x + y ≤ 1

def Q : HPolyhedron (ℝn 2) :=
  (HPolyhedron.mk {h1, h2, h3} (Set.toFinite _)) -- Or Set.toFinite ({h1, h2, h3} : Set (Halfspace (ℝn 2)))
```

Once both are defined, compare them: `P.carrier` and `Q.carrier` are the same triangle, one described by its vertices and the other by three halfspaces. That equality is the Minkowski-Weyl theorem for this single example. Note also that `Q` is bounded, so it is in fact an `HPolytope`.


**Extra Challenge:** Define how to translate an `HPolyhedron` inside its namespace. Like `VPolytope.translate`, this is needed for the proof of the Minkowski-Weyl theorem.

```lean
def translate (P : HPolyhedron E) (v : E) : HPolyhedron E :=
  {halfspaces := (fun h : Halfspace E =>
        { normal := h.normal,
          offset := h.offset + inner ℝ h.normal v
        }) '' P.halfspaces
   finite := P.finite.image _
  }
```


Duality
===
A key tool in proving the Minkowski-Weyl Theorem is duality.

Some version of duality is already implemented in Mathlib, but it is too general and difficult to parse for our purposes, so we implement our own:

```lean
def dual (P : Set E) : Set E :=
  ⋂ x ∈ P, (Halfspace.mk x 1).carrier
```

One can observe that duality sends points to halfspaces.

Note that we do not need to exclude `0` from `P`: the point `0` contributes the halfspace `{y | inner ℝ 0 y ≤ 1}`, which is all of `E`, so it does not change the intersection.


The dual of a VPolytope
===
One can guess directly from the definition of duality that the dual of a VPolytope is an HPolyhedron since points become halfspaces.

Therefore, we can define the dual of a `VPolytope` as:

```lean
def VPolytope.dual (P : VPolytope E) : HPolyhedron E :=
  { halfspaces := (fun x => Halfspace.mk x 1) '' P.points,
    finite := P.finite.image _ }
```

And there is the third underscore. It replaces the function being applied, `fun x => Halfspace.mk x 1`. Note that `P.finite` sits before the dot, so it is already filling the other argument of `Set.Finite.image`.

A natural theorem would then be:

```lean
theorem dual_of_VPolytope (P : VPolytope E) : dual P.carrier = P.dual.carrier := by
--brief
  ext y
  simp only [dual, VPolytope.dual, VPolytope.carrier, HPolyhedron.carrier, Halfspace.carrier,
    Set.mem_iInter, Set.mem_image, Set.mem_ofPred_eq,
    forall_exists_index, and_imp]
  constructor
  · -- every generator lies in the polytope, so it satisfies the dual inequality
    intro hy i x hx rfl
    exact hy x (subset_convexHull ℝ P.points hx)
  · -- the inequality holds on the generators, hence on their convex hull
    intro hy z hz
    have hsub : P.points ⊆ ((Halfspace.mk y 1 : Halfspace E).carrier) := by
      intro x hx
      have hx' : inner ℝ x y ≤ 1 := hy (Halfspace.mk x 1) x hx rfl
      simpa [Halfspace.carrier, real_inner_comm y x] using hx'
    have hz' : z ∈ ((Halfspace.mk y 1 : Halfspace E).carrier) :=
      convexHull_min hsub (Halfspace.isConvex (Halfspace.mk y 1)) hz
    simpa [Halfspace.carrier, real_inner_comm y z] using hz'
--unbrief
```

This is a long Lean proof, so we are not doing it today. If you want, you can try to generate a proof using AI.


Exercise 4: properties of duality
===
Prove the following basic properties of duality.

```lean
namespace dual

theorem zero_mem (P : Set E) : (0 : E) ∈ dual P := by
  rw [dual]
  simp only [Set.mem_iInter, Halfspace.carrier]
  intro x hx
  simp

theorem isAntitone {A B : Set E} (h : A ⊆ B) : dual B ⊆ dual A := by
  dsimp [dual]
  intro y hy
  simp only [Set.mem_iInter] at hy ⊢
  intro x hx
  exact hy x (h hx)

end dual
```

It is also true that the dual of a set is closed and convex, and should follow directly from the Halfspace properties.


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
  obtain ⟨a, ha⟩ : ∃ a : E, ∀ x : E, f x = inner ℝ a x := by
    -- The map toDualMap is surjective for complete spaces (E is finite dimensional, hence complete).
    -- So there exists `a` such that `f = toDualMap ℝ E a`.
    have hsurj : Function.Surjective (InnerProductSpace.toDualMap ℝ E) :=
      LinearIsometryEquiv.surjective (InnerProductSpace.toDual ℝ E)
    obtain ⟨a, rfl⟩ := hsurj f
    use a
    intro x
    -- Now show: (toDualMap ℝ E a) x = inner ℝ a x
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

This is not a new theorem. Mathlib already proves it, as `geometric_hahn_banach_compact_closed`. What differs is the shape of the conclusion: Mathlib separates the two sets with a continuous linear *functional* `f`, whereas we want a *vector* `a` together with the inner product `inner ℝ a x`. The two formulations are interchangeable here by the Riesz representation theorem, which applies because `E` is finite dimensional and hence complete. So the proof above is mostly bookkeeping: invoke the Mathlib result, convert `f` into `a`, and take the midpoint of the two bounds as the separating constant.


More main theorems
===

```lean
theorem dual_of_dual
  (X : Set E) :
  dual (dual X)
  = closure
    (convexHull ℝ
    (X ∪ ({0} : Set E))) := sorry

theorem HPolytope_is_VPolytope :
  ∀ P : HPolytope E,
  ∃ Q : VPolytope E, P.carrier = Q.carrier := sorry

theorem VPolytope_is_HPolytope [Nontrivial E] :
  ∀ P : VPolytope E,
  ∃ Q : HPolytope E, P.carrier = Q.carrier := sorry
```

Note the asymmetry between the last two statements: only `VPolytope_is_HPolytope` assumes `Nontrivial E`, which rules out the degenerate space `E = {0}`. Whether that hypothesis is genuinely needed is one of the things writing the proof will settle.

```lean
--hide
end
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

