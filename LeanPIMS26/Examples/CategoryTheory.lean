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

namespace LeanW26.CategoryTheory

/-
Category Theory --Nat Hurtig
===
-/

/-
Why Category Theory
===

Structures so far have mostly been a **carrier type** plus **operations on that carrier**:

- `Group G` has `op : G → G → G`
- `Poset α` has `le : α → α → Prop`
- `Ring R`, `Lattice α`, `Field F`, ...

Categories don't fit into this pattern! There are multiple types. This causes
dependent typing woes, and universes make a return when we want to model
certain categories.

Additionaly, Mathlib's category theory definitions are different from the
"straightforward" way to define math ideas seen in this course. We'll take a
look at Mathlib's definitions at the end.

This lecture is focused on *definitions and statements*, not proofs: LLMs might
be great for filling in a `sorry`, but humans need to make sure top-level
definitions represent the right things!
-/

/-
What We Are Not Doing
===

We won't be diving deep into category theory. The plan:
- Categories themselves
- Functors between categories

Most of our time will be spent on Lean and Mathlib, using category theory as a
vehicle for prodding at them. Nat is a computer scientist, and not a category
theorist!
-/

/-
The Definition
===

A category consists of

- a collection of **objects**
- for each pair of objects `A B`, a collection of **arrows** from `A` to `B`
- a way to **compose** arrows, when the target of one is the source of the next
- an **identity** arrow on every object

subject to: composition is associative, and identities do nothing.

Kinda like a monoid over arrows, but composition is only defined for arrows
whose objects line up.
-/

/-
The Definition in Lean
===

The type of objects is a *parameter*. The arrows are a field, indexed by pairs of
objects. Objects and arrows each are allowed to live in their own universes.
-/

structure Category.{v, u} (Obj : Type u) where
  Hom  : Obj → Obj → Type v
  id   : (A : Obj) → Hom A A
  comp {A B C : Obj} : Hom A B → Hom B C → Hom A C
  id_comp : ∀ {A B} (f : Hom A B), comp (id A) f = f
  comp_id : ∀ {A B} (f : Hom A B), comp f (id B) = f
  assoc   : ∀ {A B C D} (f : Hom A B) (g : Hom B C) (h : Hom C D),
              comp (comp f g) h = comp f (comp g h)

/-
`Hom` is a *function*: given two objects, it returns a type. So `Hom A B` is just some type, in the universe `v`.
-/

--hide
universe u v
--unhide

/-
Conventions
===

**Composition order.** `comp f g` means "`f`, then `g`": diagrammatic order,
following the arrows. Others write `g ∘ f` instead; "`g` after `f`".

-/

#check Category.comp -- self.Hom A B → self.Hom B C → self.Hom A C

/-
**Universe order.** Lean binds universes by default in order of first
appearance in definitions, and `Obj : Type u` comes first, so you'd get
`Category.{u, v}`. When you write `Category X`, Lean can read `u` straight off
`X`, but nothing determines `v`. Putting `v` first lets you write `Category.{7}
X` instead of `Category.{_, 7} X`.
-/

/-
Exercise: The Category of Types
===

Lean itself forms a category!
- Objects are types
- Arrows are functions
- Identity and composition are identity and composition
-/

def Types : Category (Type u) where
  Hom A B := A → B -- the type of functions from `A` to `B`
  id _A := fun a => a -- aka `id`, the identity function on `_A`
  comp f g := fun a => g (f a) -- could have been written g ∘ f
  id_comp _A := rfl
  comp_id _A := rfl
  assoc _f _g _h := rfl

/-
Revisiting Monoids
===

The category axioms (identity, association) look close to the monoid axioms:
-/

namespace Temp

class Monoid (M : Type u) where
  mul : M → M → M -- morally composition of arrows
  one : M -- morally identity arrows
  mul_assoc {a b c : M} : mul (mul a b) c = mul a (mul b c)
  mul_id_left {a : M}   : mul one a = a
  mul_id_right {a : M}  : mul a one = a

end Temp

/-
If the elements of the monoid correspond to the arrows, what are the objects?
- Arrows compose whenever objects line up
- In a monoid, arrows always compose
- The objects must always line up!
-/

/-
A Monoid Is a One-Object Category
===

Use `Unit`, with its only member `() : Unit`:
-/

def OfMonoid (M : Type v) [Temp.Monoid M] : Category.{v} Unit where
  Hom _ _ := M -- the arrows are the monoid elements
  id _ := Temp.Monoid.one
  comp f g := Temp.Monoid.mul f g
  id_comp _ := Temp.Monoid.mul_id_left
  comp_id _ := Temp.Monoid.mul_id_right
  assoc _ _ _ := Temp.Monoid.mul_assoc

/-
Every object placeholder in the above definition is `() : Unit`, the only
object in the category.
-/

/-
Going in Reverse
===

A category with exactly one object *is* a monoid. With the last slide's other
direction, we have a *kind-of* bijection between monoids and one-object categories.

`[Unique A]` says `A` has exactly one element, and `default` is that element.
-/

instance {A : Type u} (C : Category A) [Unique A] : Temp.Monoid (C.Hom default default) where
  one := C.id default
  mul x y := C.comp x y
  mul_assoc := C.assoc _ _ _
  mul_id_left := C.id_comp _
  mul_id_right := C.comp_id _

/-
In fact, given *any* `X : A`, the arrows `C.Hom X X` form a monoid!

The "bijection" is not really an `Equiv` because the unique object type is
dropped in the `Monoid`. Possible patches to get true bijection: `Monoid` is
equivalent to the categories over `Unit`, or single-object categories are
equivalent to `Monoid`s bundled with some unique type.
-/

/-
Exercise: A Preorder Is a Thin Category
===

<ex/> Define `OfPreorder (X : Type u) [Preorder X] : Category X where` ...

Hint: unlike `Monoid`, the *objects* here are the elements of `X`. Then define
arrows using the preorder's comparator: one arrow `Hom A B` iff `A ≤ B`.

Mathlib's `Preorder` is the `Poset` of the Relations deck minus antisymmetry: `≤` is
reflexive (`le_refl`) and transitive (`le_trans`), but two elements can each be below the
other without being equal.

If you get an error about mismatched types, you've successfully followed the
slightly misleading hint!

-/

/-
Universes have Returned
===

Writing
```lean
def OfPreorder (X : Type u) [Preorder X] : Category X where
  Hom A B := A ≤ B
```
yields

"`A ≤ B` has type `Prop` of sort `Type` but is expected to have type `Type
?u.8` of sort `Type (?u.8 + 1)`".

Making sense of the universe synonyms:
```
    Sort 0 = Prop
    Sort 1 = Type 0 = Type
    Sort 2 = Type 1
```

`Hom` needs to return a `Type v`, which has sort `Type (v + 1)`. We're suppling
`A ≤ B`, of type `Prop`, which has sort `Type 0`. Lean can't solve `0 = v + 1`.

Plainly, we need a type, not a proposition, and `A ≤ B` is a proposition!

-/

/-
PLift Saves the Day
===

`PLift` has a one-field structure that puts the proof in a `Type`-flavored box.
Constructor `PLift.up` and projection `PLift.down`:
```lean
    PLift.up   : α → PLift α
    PLift.down : PLift α → α
```
We can now define `Hom A B := PLift (A ≤ B)`. Because `PLift (A ≤ B) : Type`
the whole category has arrow universe `v := 0`.
-/

def OfPreorder (X : Type u) [Preorder X] : Category.{0} X where
  Hom A B := PLift (A ≤ B)
  id A := ⟨le_refl A⟩
  comp f g := ⟨le_trans f.down g.down⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-
So ends our core definitions involving `Category`.
-/

/-
Functors
===

Categories have structure, so there should be structure-preserving maps between them.
A **functor** `F : Functor C D` sends objects to objects and arrows to arrows: it takes
an arrow `Hom A B` to an arrow `Hom (F A) (F B)`, and preserves identities and
composition. Mathlib writes this type using `⥤` (like many things in Mathlib,
you can type the symbol using `\functor`).

The *type* of `map` uses the *value* of `obj`. This will cause us some trouble later!
-/

structure Functor.{v₁, v₂, u₁, u₂} {X : Type u₁} {Y : Type u₂}
    (C : Category.{v₁} X) (D : Category.{v₂} Y) where
  obj : X → Y
  map {A B : X} : C.Hom A B → D.Hom (obj A) (obj B)
  map_id : ∀ (A : X), map (C.id A) = D.id (obj A)
  map_comp : ∀ {A B E : X} (f : C.Hom A B) (g : C.Hom B E),
               map (C.comp f g) = D.comp (map f) (map g)

--hide
universe u₁ u₂ u₃ v₁ v₂
--unhide

/-
Identity and Composition
===

Functors compose, and every category has an identity functor. Neither
definition is too much proof burden.
-/

def Functor.id {X : Type u₁} (C : Category X) : Functor C C where
  obj A := A -- identity on objects
  map f := f -- identity on arrows
  map_id _ := rfl
  map_comp _ _ := rfl

def Functor.comp {X : Type u₁} {Y : Type u₂} {Z : Type u₃}
    {C : Category X} {D : Category Y} {E : Category Z}
    (F : Functor C D) (G : Functor D E) : Functor C E where
  obj A := G.obj (F.obj A)
  map f := G.map (F.map f)
  map_id A := by rw [F.map_id, G.map_id]
  map_comp f g := by rw [F.map_comp, G.map_comp]

/-
Exercise: Functors You Already Have
===

<ex/> A monoid homomorphism is a functor between the corresponding
one-object categories.
-/

def OfMonoidHom {M N : Type u} [Temp.Monoid M] [Temp.Monoid N]
    (f : M → N)
    (h_one : f Temp.Monoid.one = Temp.Monoid.one)
    (h_mul : ∀ a b, f (Temp.Monoid.mul a b) = Temp.Monoid.mul (f a) (f b)) :
  Functor (OfMonoid M) (OfMonoid N) where
    --hide
    obj := sorry
    map := sorry
    map_id := sorry
    map_comp := sorry
    --unhide

/-
<ex/> A monotone map is exactly a functor between the corresponding preorder
categories. Build that one too (`Monotone f` unfolds to `a ≤ b → f a ≤ f b`).
-/

def OfMonotone {X Y : Type u} [Preorder X] [Preorder Y]
    (f : X → Y) (hf : Monotone f) :
  Functor (OfPreorder X) (OfPreorder Y) where
    --hide
    obj := sorry
    map hAB := sorry
    map_id := sorry
    map_comp := sorry
    --unhide

/-
When Are Two Functors Equal?
===

```lean
theorem Functor.ext_naive {X : Type u₁} {Y : Type u₂} {C : Category X} {D : Category Y}
    (F G : Functor C D)
    (hobj : ∀ A, F.obj A = G.obj A)
    (hmap : ∀ {A B} (f : C.Hom A B), F.map f = G.map f) : F = G := sorry
```

This fails to **typecheck**:

```
Type mismatch
  G.map f
has type
  D.Hom (G.obj A) (G.obj B)
but is expected to have type
  D.Hom (F.obj A) (F.obj B)
```

`F.map f` and `G.map f` have different types, and are the same type only if we
already know `F.obj = G.obj`. Unfortunately, `hobj` is a hypothesis, not
something the elaborator uses automatically while it is still reading the
statement.
-/

/-
Transport Can Save Us
===

The repair is to say it *with* the object equality: transport `G.map f` along
`hobj` so that both sides land in the same type.

`cases ... with | mk ...` splits each functor into its four fields, and `subst` then
replaces `Gobj` by `Fobj` everywhere once we know they are equal.
-/

theorem Functor.ext {X : Type u₁} {Y : Type u₂} {C : Category X} {D : Category Y}
    (F G : Functor C D)
    (hobj : ∀ A, F.obj A = G.obj A)
    (hmap : ∀ {A B} (f : C.Hom A B), F.map f = (hobj B ▸ hobj A ▸ G.map f)) : F = G := by
  cases F with | mk Fobj Fmap Fmap_id Fmap_comp =>
  cases G with | mk Gobj Gmap Gmap_id Gmap_comp =>
  have objects_equal : Fobj = Gobj := funext hobj
  subst objects_equal -- rewrites Gmap's type!
  simp
  ext
  apply hmap

/-
But this is dissatisfying. Must we deal with transport every time we want to
show equality between dependently typed structures?
-/

/-
Mathlib's Answer: `eqToHom`
===

Mathlib states the same theorem, but not directly with `▸`. It turns the object
equality into an actual arrow. Every category has these for free:
-/

def Category.eqToHom {X : Type u₁} (C : Category X) {A B : X} (h : A = B) : C.Hom A B :=
  h ▸ C.id A

/-
so `F.map f` gets compared not with `G.map f`, but with `G.map f` composed on
both sides (≫ is arrow composition in Mathlib) with `eqToHom` arrows:

```lean
theorem ext {F G : C ⥤ D} (h_obj : ∀ X, F.obj X = G.obj X)
    (h_map : ∀ X Y f,
      F.map f = eqToHom (h_obj X) ≫ G.map f ≫ eqToHom (h_obj Y).symm := by cat_disch) :
    F = G
```

`eqToHom`'s docstring:

> *An equality `X = Y` gives us a morphism `X ⟶ Y`. It is typically better to
> use this, rather than rewriting by the equality then using `𝟙 _`, which
> usually leads to dependent type theory hell.*

-/

/-
Even `eqToHom` isn't good enough
===

Mathlib puts this `Functor.ext` lemma in `Mathlib/CategoryTheory/EqToHom.lean`
rather than with the other functor lemmas, with this docstring:

> *Proving equality between functors. This isn't an extensionality lemma,
> because usually you don't really want to do this.*

Even though `eqToHom` avoids transport at the surface, `eqToHom` itself uses
transport. Depending on your goals, transport can sometimes be a flag that
something has gone wrong in the formalization.

Category theorists prefer a different, weaker equivalence relation on functors.
-/

/-
The Right Notion: "equal" doesn't always mean `Eq`
===

We attempted to write `F = G`, but that brought about all sorts of issues with
dependent types. This is because straight `Eq` equality between functors is **too
strong** for our category-theoretic purposes; we really don't care whether
`F.obj = G.obj`!

Instead, we care just about whether the **arrows** form the right shape.
-/

/-
Whirlwind: Functor "sameness"
===

A functor `F : C ⥤ D` is a transformation from one category to another, with
composition and identities.

A *natural transformation* `η : F ⟶ G` is a transformation from one **functor**
to another, with composition and identities.

Two functors are **isomorphic** whenever there exist natural transformations
`η : F ⟶ G` and `ε : G ⟶ F` where both
* `η` composed with `ε` is the identity natural transformation, and
* `ε` composed with `η` is the identity natural transformation.

Hence two functors `C ⥤ D` with provably different object maps can be isomorphic!
-/

/-
The Lessons from Functors
===
When dealing with dependent types, Lean can get in the way of stating the
properties we think we want.

Transport `▸` can help us state valid math, but it can lead to *dependent type
theory hell*; defining tools like `eqToHom` helps you sweep transport under the
rug.

The best option, if it's available, is to avoid transport altogether and seek
an alternative, domain-specific version of equality like `Functor`'s
isomorphisms.
-/

/-
Topic Change: What Universe Is `Types` In?
===

We built `Types`, the category with `Type u` as objects and functions as
arrows, earlier. What universe does it live in?
-/

set_option pp.universes true in -- trick to show universes in next statement
#check @Types.{u} -- Category.{u, u + 1}

/-
Arrows in `Type u`, objects in `Type (u + 1)`.

The objects *are* the types with type `Type u`, and `Type u : Type (u + 1)`.
The arrows are functions `A → B` with `A B : Type u`, and a function type lands
in the `imax` of its two universes, so just `u`.

So `Types` isn't one category, but a family of categories, one for each `u`.
-/

/-
Universe of `Category.{v, u}`
===

**Functions** land in the `imax` of their two universes (functions returning
`Prop` are always `Prop`).

**Structures** land in the `max` of their *fields'* universes, and are never in
`Prop`. If it has a field `n : ℕ`, then its universe is at least `Type 0`
because `ℕ : Type 0`. If it *stores* a type `obj : Type u`, then because `Type
u : Type (u + 1)`, the structure's universe is at least `Type (u + 1)`.

**Parameters and indices** don't directly count until they're used elsewhere in
the definition. `Category` takes its objects as a parameter.

Combining these together, `Category` stores three non-`Prop` fields:
* `Hom : Obj → Obj → Type v`, which lands in `Type (max u (v + 1))` because
`Obj : Type u` and `Type v : Type (v + 1)`.
* `id : (A : Obj) → Hom A A`, which lands in `Type (max u v)` because `Obj :
Type u` and `Hom _ _ : Type v`.
* `comp {A B C : Obj} : Hom A B → Hom B C → Hom A C`, which lands in `Type (max
u v)` because `Obj : Type u` and `Hom _ _ : Type v`.
-/

set_option pp.universes true in
#check Category -- Type (max u (v + 1))

/-
Exercise: Universe of `Functor`
===

<ex/> Take a moment to calculate the universe of `Functor` by hand:

```lean
structure Functor.{v₁, v₂, u₁, u₂} {X : Type u₁} {Y : Type u₂}
    (C : Category.{v₁} X) (D : Category.{v₂} Y) where
  obj : X → Y
  map {A B : X} : C.Hom A B → D.Hom (obj A) (obj B)
  map_id : ∀ (A : X), map (C.id A) = D.id (obj A)
  map_comp : ∀ {A B E : X} (f : C.Hom A B) (g : C.Hom B E),
               map (C.comp f g) = D.comp (map f) (map g)
```
-/

set_option pp.universes true in
#check @Functor.{v₁, v₂, u₁, u₂} -- what comes out here?

/-
Moving Up in the Universe Hierarchy
===

Every type in `Type u` *ought* to be a type in `Type (u+1)`. There isn't an
automatic coercion: Lean's universes are **non-cumulative***.
-/

#check_failure (fun (α : Type 0) => (α : Type 1)) -- α can't be both Type 0 and Type 1

/-
Just like PLift saved us by lifting `Prop` to `Type 0`, so `ULift` lifts `Type
s` to `Type (max s r)`, effectively allowing us to increase the universe level
of anything:
-/

#check ULift -- ULift.{r, s} (α : Type s) : Type (max s r)

/-
Back to category theory: this forms a functor from one `Types` to another!
-/

def uliftFunctor : Functor Types.{u} Types.{max u v} where
  obj X := ULift.{v} X
  map f := fun x => ULift.up (f x.down)
  map_id _ := rfl
  map_comp _ _ := rfl

/-
\*Rocq, an alternative to Lean in some manners, has cumulative universes! So is
a language design choice, not some dependent type theory snag.
-/

/-
The Category of Categories
===

Functors map between categories; they have identities and composition. Sounds like a category where the objects are categories and the arrows are functors!
Because `Category` is parameterized by an object type, we **bundle** the object with `Category` to form a "category over an arbitrary object" type:
-/

def Cats : Category (Σ X : Type u, Category.{v} X) where
  Hom C D := Functor C.2 D.2
  id C := Functor.id C.2
  comp F G := Functor.comp F G
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

set_option pp.universes true in
#check Cats -- arrows are (max u v); objects are (max (u + 1) (v + 1))

/-
Arrows in `max u v`: a functor is no bigger than the categories it joins.

Objects are in `max (u+1) (v+1)`: The `v + 1` comes from `Category.{v}`, and
the `u + 1` comes from storing the `X : Type u`.
-/

/-
`Cats` Is Not One of Its Own Objects
===

`Cats.{u, v}` is a category. Is it one of the categories it's about?

`Cats` **is** an object of **a different** `Cats` higher in the universe hierarchy:
```lean
example : Σ X : Type (max (u+1) (v+1)), Category.{max u v} X := ⟨_, Cats.{u,v}⟩
```

But it's not one of its own objects:
```lean
example : Σ X : Type u, Category.{v} X := ⟨_, Cats.{u,v}⟩
```
-/
--hide
-- example : Σ X : Type u, Category.{v} X := ⟨_, Cats.{u,v}⟩
--unhide
/-
```
Application type mismatch: The argument
  Cats
has type
  Category.{max u v, max (max (v + 1) u) (u + 1)} ((X : Type u) × Category X)
...
but is expected to have type
  Category.{v, u} ?m.4
```

Girard's paradox avoided!
-/

/-
What does Mathlib do?
===

It's edifying to see how "the pros" define category theory in Mathlib. They use
three cascading definitions where we used one to define a category:

```lean
class Quiver (V : Type u) where
  Hom : V → V → Type v -- ⟶ (\hom) is used for notation (different from \to!)

class CategoryStruct (obj : Type u) : Type max u (v + 1) extends Quiver.{v} obj where
  id   : ∀ X : obj, Hom X X -- 𝟙 (\b1) notation
  comp : ∀ {X Y Z : obj}, (X ⟶ Y) → (Y ⟶ Z) → (X ⟶ Z) -- ≫ (\gg) notation

class Category (obj : Type u) : Type max u (v + 1) extends CategoryStruct.{v} obj where
  id_comp : ∀ {X Y : obj} (f : X ⟶ Y), 𝟙 X ≫ f = f := by cat_disch
  comp_id : ∀ {X Y : obj} (f : X ⟶ Y), f ≫ 𝟙 Y = f := by cat_disch
  assoc   : ∀ {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),
              (f ≫ g) ≫ h = f ≫ g ≫ h := by cat_disch
```

Three differences: multiple layered definitions, `class` instead of
`structure`, and the `:= by cat_disch`.
-/

/-
Why Three Definitions?
===

A **quiver** is a category with everything removed except the objects and
arrows: no identity, no composition, no laws. In other words, a directed
multigraph:

```lean
class Quiver (V : Type u) where
  Hom : V → V → Type v
```

Mathlib separates `Quiver` from `Category` because there are some definitions
that use `Quiver` alone, and don't require the categorical structure.
Separating out `Quiver` doesn't affect downstream `Category` use; it freely
enables other definitions.
-/

/-
The Free Category on a Quiver
===

Take any quiver and build a category from it: same objects, and an arrow `A ⟶
B` is a **path**: a finite chain of quiver edges from `A` to `B`. Identity is
the empty path, composition is concatenation.

```lean
variable [Quiver V] -- assume a quiver on `V` is in scope

def Paths (V : Type u₁) : Type u₁ := V -- a type synonym; we'll see this later

instance : Category.{max u₁ v₁} (Paths V) where
  Hom := fun X Y : V => Quiver.Path X Y
  id _ := Quiver.Path.nil
  comp f g := Quiver.Path.comp f g
  -- hmm... why didn't Mathlib prove the identity and association laws?
```

Adjoint functors arise:
```lean
def forget : Cat.{v, u} ⥤ Quiv.{v, u}
def free   : Quiv.{v, u} ⥤ Cat.{max u v, u}
def adj    : Cat.free ⊣ Quiv.forget
```

Similarly, `CategoryStruct` broadens definitions that don't depend on the
categorical laws, like `eqToHom`.
-/

/-
Why a `class` and Not a `structure`?
===

Ours takes the category as an argument, so we have to name it and pass it around:

```lean
example (X : Type u) (C : Category.{v} X) (A B E : X)
    (f : C.Hom A B) (g : C.Hom B E) : C.Hom A E := C.comp f g
```

Mathlib makes it an instance. Once `[Category C]` is in scope, we never mention it
again: the objects **are** the type `C`, and `⟶` and `≫` find the instance themselves.

```lean
example {C : Type u} [Category.{v} C] (A B E : C)
    (f : A ⟶ B) (g : B ⟶ E) : A ⟶ E := f ≫ g
```

If `C` is a specific type with an existing `Category` instance, then the
`[Category C]` can be omitted entirely!

-/


/-
The Cost: One Category Per Type
===

`ℕ` is already a category, via its `Preorder`. Try to also make it a category by
divisibility:

```lean
example (a b : ℕ) (h : a ≤ b) : a ⟶ b := homOfLE h    -- fine

instance dvdCat : Category ℕ where
  Hom a b := ULift (PLift (a ∣ b))
  id a := ⟨⟨dvd_refl a⟩⟩
  comp f g := ⟨⟨dvd_trans f.down.down g.down.down⟩⟩

example (a b : ℕ) (h : a ≤ b) : a ⟶ b := homOfLE h    -- the same line a second time
```
The second line fails to typecheck!
```
Type mismatch
  homOfLE h
has type       @Quiver.Hom ℕ (Preorder.smallCategory ℕ).toQuiver a b
but is expected to have type
               @Quiver.Hom ℕ catToReflQuiver.toQuiver a b
```

The same line fails **the second time only**. Typeclass synthesis resolves the
new category instance the second time, and doesn't try the first instance after
the second fails to typecheck.

-/

/-
Typeclass Synthesis is (largely) Uncontrollable
===

From personal experience: this is very annoying! And it is working as intended.
Someone filed this as a bug in 2022, having hit it with `Category` and `Groupoid`
on the same type, and got told:

> This is the intended behavior in Lean 4. For any argument of the form `[...]` a
> type class resolution problem is created even if the argument value can be
> inferred by typing constraints.
>
> --- Leonardo de Moura

--hide
https://github.com/leanprover/lean4/issues/952
--unhide

One can somewhat control which instances get selected via `priority` and `local
instance` within statements, but it's finicky.
-/

/-
The Fix: Type Synonyms
===

```lean
def NatDvd : Type := ℕ
def NatDvd.val (n : NatDvd) : ℕ := n

instance : Category NatDvd where
  Hom a b := ULift (PLift (a.val ∣ b.val))
  id a := ⟨⟨dvd_refl a.val⟩⟩
  comp f g := ⟨⟨dvd_trans f.down.down g.down.down⟩⟩
```

Both now coexist:
```lean
example (a b : ℕ)     (h : a ≤ b)         : a ⟶ b := homOfLE h
example (a b : NatDvd) (h : a.val ∣ b.val) : a ⟶ b := ⟨⟨h⟩⟩
```

`NatDvd` is *definitionally* `ℕ`, but instance synthesis won't unfold a `def`
to find instances, so `NatDvd` inherits **nothing**. Not `Category` (intended),
but also not `Dvd`, `Monoid`, or `DecidableEq`. You have to wire those up
yourself if you want them.

Mathlib uses type synonyms frequently for this reason! Another fix is defining
instances locally to a definition, but that gets old fast.
-/

/-
Why `:= by cat_disch`?
===

Look again at the law fields in Mathlib's `Category`: they end in `:= by
cat_disch`. A `:= by tac` in a *field* position is an **auto-param**: omit the
field when you build the structure and Lean runs `tac` to produce it. Our three
laws had to be proved by hand in every example, usually by `rfl`. Mathlib has
seen the pattern, and developed `cat_disch` to dispatch "easy" category theory
goals.

`cat_disch` is used everywhere in the category theory section of Mathlib. It
uses a version of `aesop` with specifically registered rules; it also has a
`grind` mode.

The size of Mathlib justifies the presence of such a tactic. If fields are
renamed, or their contents are changed such that their proofs are still easy,
then `cat_disch` keeps the proofs checking without any source code changes.
-/

/-
Where the Category Theory Goes
===

We didn't get to much category theory. The rest, and where it lives in Mathlib:

- **Natural transformations**, `CategoryTheory/NatTrans.lean`. The honest answer to
  "when are two functors the same," which we left open.
- **Limits and colimits**, `CategoryTheory/Limits/`. Products, equalizers, pullbacks.
- **Adjunctions**, `CategoryTheory/Adjunction/`. We stated one and did not unpack it.
- **Yoneda**, `CategoryTheory/Yoneda.lean`.

My own interests in category theory are in string diagrams for monoidal
categories: the topology of *twisted involutive* monoidal categories represents
exactly the equivalences of machine knitted objects, so I use them to provide
formal semantics for machine knitting code! I'm currently working on an
optimizing compiler that makes fancy sweaters real fast using category theory.
-/

/-
Key Takeaways
===

**Scale your encoding by what you need to *state*.** Notation and nested
definitions can be a great way to focus on what matters for mature projects,
but a time sink for new ones. A typeclass buys quick notation and synthesis but
costs you one instance per type.

**Equality of dependent data is usually a code smell.** When the statement will
not typecheck, don't jump to repairing the equality. Look for a structure that
replaces it.

**A type gets one findable instance per class.** The go-to escape hatch is a
type synonym, and it costs you every other instance on that type. That is what
`Paths`, `Cᵒᵖ`, and many others are.

**Read Mathlib code, even if you don't use it.** The maintainers have made
mistakes, fought battles, and documented their journeys. Take the free
guidance!
-/

--hide
end LeanW26.CategoryTheory
--unhide
