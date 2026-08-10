- `(x, n)` is glued to `(x, n + 1)`: on even lines along the positive half,
on odd lines along the negative half. 
```lean
def glueAt (n : ℤ) (x : ℝ) : Prop := (Even n ∧ 0 < x) ∨ (Odd n ∧ x < 0)

lemma glueAt.ne_zero {n : ℤ} {x : ℝ} (h : glueAt n x) : x ≠ 0 := by
  rcases h with ⟨-, h⟩ | ⟨-, h⟩
  · exact h.ne'
  · exact h.ne

lemma glueAt.not_succ {n : ℤ} {x : ℝ} (h : glueAt n x) : ¬glueAt (n + 1) x := by
  simp only [glueAt, Int.even_iff, Int.odd_iff] at h ⊢
  rintro (⟨h1, hx⟩ | ⟨h1, hx⟩) <;> rcases h with ⟨h2, hx'⟩ | ⟨h2, hx'⟩ <;> first | omega | linarith

lemma glueAt_shift {n k : ℤ} {x : ℝ} : glueAt (n + 2 * k) x ↔ glueAt n x := by
  have h : (n + 2 * k) % 2 = n % 2 := by omega
  simp only [glueAt, Int.even_iff, Int.odd_iff, h]
```
- `b` is the glued successor of `a`. 
```lean
def glued (a b : ℝ × ℤ) : Prop := b = (a.1, a.2 + 1) ∧ glueAt a.2 a.1

lemma glued.not_chain {a b c : ℝ × ℤ} (h1 : glued a b) (h2 : glued b c) : False := by
  refine h1.2.not_succ ?_
  have hb : b = (a.1, a.2 + 1) := h1.1
  have := h2.2
  rw [hb] at this
  exact this

lemma glued_right_unique {a b c : ℝ × ℤ} (h1 : glued a b) (h2 : glued a c) : b = c := by
  rw [h1.1, h2.1]

lemma glued_left_unique {a b c : ℝ × ℤ} (h1 : glued a c) (h2 : glued b c) : a = b := by
  have h := h1.1.symm.trans h2.1
  injection h with hfst hsnd
  exact Prod.ext hfst (by omega)
```
- Two points of `ℝ × ℤ` are identified iff they are equal or one is the glued
successor of the other. 
```lean
def rel (a b : ℝ × ℤ) : Prop := a = b ∨ glued a b ∨ glued b a

def setoid : Setoid (ℝ × ℤ) where
  r := rel
  iseqv := by
    refine ⟨fun _ ↦ .inl rfl, ?_, ?_⟩
    · rintro a b (rfl | h | h)
      · exact .inl rfl
      · exact .inr (.inr h)
      · exact .inr (.inl h)
    · rintro a b c (rfl | h1 | h1) h2
      · exact h2
      · rcases h2 with rfl | h2 | h2
        · exact .inr (.inl h1)
        · exact (h1.not_chain h2).elim
        · exact .inl (glued_left_unique h1 h2)
      · rcases h2 with rfl | h2 | h2
        · exact .inr (.inr h1)
        · exact .inl (glued_right_unique h1 h2)
        · exact (h2.not_chain h1).elim

end ZigZag
```
- The zigzag: countably many real lines, each glued to the next along alternating
half-lines. This is the universal cover of the line with two origins. 
```lean
def ZigZag := Quotient ZigZag.setoid

instance : TopologicalSpace ZigZag := inferInstanceAs (TopologicalSpace (Quotient _))

namespace ZigZag
```
- The point of `ZigZag` at coordinate `x` on line `n`. 
```lean
def mk (x : ℝ) (n : ℤ) : ZigZag := Quotient.mk setoid (x, n)

lemma mk_eq_mk {x y : ℝ} {n m : ℤ} : mk x n = mk y m ↔ rel (x, n) (y, m) :=
  ⟨fun h ↦ Quotient.exact h, fun h ↦ Quotient.sound h⟩

lemma continuous_mk : Continuous (Quotient.mk setoid : ℝ × ℤ → ZigZag) :=
  continuous_quotient_mk'
```
! ### The ℤ-action by shifting two lines 
- Shift by `2 * k` lines. 
```lean
def shiftFun (k : ℤ) (a : ℝ × ℤ) : ℝ × ℤ := (a.1, a.2 + 2 * k)

lemma glued_shift {k : ℤ} {a b : ℝ × ℤ} (h : glued a b) : glued (shiftFun k a) (shiftFun k b) := by
  obtain ⟨rfl, hg⟩ := h
  exact ⟨Prod.ext rfl (by simp only [shiftFun]; omega), glueAt_shift.mpr hg⟩

lemma rel_shift {k : ℤ} {a b : ℝ × ℤ} (h : rel a b) : rel (shiftFun k a) (shiftFun k b) := by
  rcases h with rfl | h | h
  · exact .inl rfl
  · exact .inr (.inl (glued_shift h))
  · exact .inr (.inr (glued_shift h))

instance : AddAction ℤ ZigZag where
  vadd k := Quotient.map (shiftFun k) fun _ _ ↦ rel_shift
  zero_vadd := by
    rintro ⟨a⟩
    exact congrArg (Quotient.mk setoid) (Prod.ext rfl (by simp [shiftFun]))
  add_vadd g h := by
    rintro ⟨a⟩
    exact congrArg (Quotient.mk setoid) (Prod.ext rfl (by simp only [shiftFun]; ring))

lemma vadd_mk (k : ℤ) (x : ℝ) (n : ℤ) : k +ᵥ mk x n = mk x (n + 2 * k) := rfl
```
! ### The covering map to the line with two origins 
- Project a line to one of the two copies of `ℝ` according to parity. 
```lean
def proj (a : ℝ × ℤ) : TwoR := if Even a.2 then .inl a.1 else .inr a.1

lemma proj_glued {a b : ℝ × ℤ} (h : glued a b) : TwoOrigins.q (proj a) = TwoOrigins.q (proj b) := by
  obtain ⟨rfl, hg⟩ := h
  have hx : a.1 ≠ 0 := hg.ne_zero
  rcases Int.even_or_odd a.2 with he | ho
  · have h1 : proj a = .inl a.1 := if_pos he
    have h2 : proj (a.1, a.2 + 1) = .inr a.1 := if_neg (by simp [he])
    rw [h1, h2]
    exact TwoOrigins.glue hx
  · have h1 : proj a = .inr a.1 := if_neg (Int.not_even_iff_odd.mpr ho)
    have h2 : proj (a.1, a.2 + 1) = .inl a.1 :=
      if_pos (Int.even_add_one.mpr (Int.not_even_iff_odd.mpr ho))
    rw [h1, h2]
    exact (TwoOrigins.glue hx).symm

lemma proj_rel {a b : ℝ × ℤ} (h : rel a b) : TwoOrigins.q (proj a) = TwoOrigins.q (proj b) := by
  rcases h with rfl | h | h
  · rfl
  · exact proj_glued h
  · exact (proj_glued h).symm
```
- The covering map. 
```lean
def p : ZigZag → TwoOrigins := Quotient.lift (fun a ↦ TwoOrigins.q (proj a)) fun _ _ ↦ proj_rel

lemma p_mk (x : ℝ) (n : ℤ) : p (mk x n) = TwoOrigins.q (proj (x, n)) := rfl

lemma isClopen_even : IsClopen {a : ℝ × ℤ | Even a.2} :=
  (isClopen_discrete {n : ℤ | Even n}).preimage continuous_snd

lemma continuous_proj : Continuous proj := by
  refine Continuous.if (fun a ha ↦ absurd ha ?_) ?_ ?_
  · rw [isClopen_even.frontier_eq]
    exact Set.notMem_empty a
  · exact continuous_inl.comp continuous_fst
  · exact continuous_inr.comp continuous_fst

lemma continuous_p : Continuous p := by
  have h : Continuous (p ∘ (Quotient.mk setoid : ℝ × ℤ → ZigZag)) :=
    TwoOrigins.continuous_q.comp continuous_proj
  exact isQuotientMap_quotient_mk'.continuous_iff.mpr h
```
! ### `mk` is an open map; sheets are open embeddings 
```lean
lemma isOpen_setOf_glueAt (k : ℤ) : IsOpen {b : ℝ × ℤ | glueAt (b.2 + k) b.1} := by
  simp only [glueAt, Set.ofPred_or, Set.ofPred_and]
  refine IsOpen.union (IsOpen.inter ?_ ?_) (IsOpen.inter ?_ ?_)
  · exact (isClopen_discrete {n : ℤ | Even (n + k)}).isOpen.preimage continuous_snd
  · exact isOpen_lt continuous_const continuous_fst
  · exact (isClopen_discrete {n : ℤ | Odd (n + k)}).isOpen.preimage continuous_snd
  · exact isOpen_lt continuous_fst continuous_const

lemma continuous_lineShift (c : ℤ) : Continuous (fun b : ℝ × ℤ ↦ (b.1, b.2 + c)) :=
  continuous_fst.prodMk
    ((continuous_of_discreteTopology (f := fun n : ℤ ↦ n + c)).comp continuous_snd)

lemma partner_up_eq (W : Set (ℝ × ℤ)) :
    {b | ∃ a ∈ W, glued a b} =
      (fun b : ℝ × ℤ ↦ (b.1, b.2 + (-1))) ⁻¹' W ∩ {b | glueAt (b.2 + (-1)) b.1} := by
  ext b
  constructor
  · rintro ⟨a, haW, rfl, hg⟩
    have key : (a.1, a.2 + 1).2 + (-1) = a.2 := by omega
    refine ⟨?_, ?_⟩ <;> simp only [Set.mem_preimage, Set.mem_ofPred_eq, key]
    · simpa using haW
    · exact hg
  · rintro ⟨hW, hg⟩
    exact ⟨(b.1, b.2 + (-1)), hW, Prod.ext rfl (by omega), hg⟩

lemma partner_down_eq (W : Set (ℝ × ℤ)) :
    {b | ∃ a ∈ W, glued b a} =
      (fun b : ℝ × ℤ ↦ (b.1, b.2 + 1)) ⁻¹' W ∩ {b | glueAt (b.2 + 0) b.1} := by
  ext b
  constructor
  · rintro ⟨a, haW, rfl, hg⟩
    refine ⟨by simpa using haW, ?_⟩
    simp only [Set.mem_ofPred_eq, add_zero]
    exact hg
  · rintro ⟨hW, hg⟩
    refine ⟨(b.1, b.2 + 1), hW, rfl, ?_⟩
    simpa using hg

lemma isOpenMap_mk : IsOpenMap (Quotient.mk setoid : ℝ × ℤ → ZigZag) := by
  intro W hW
  refine isQuotientMap_quotient_mk'.isOpen_preimage.mp ?_
  change IsOpen ((Quotient.mk setoid : ℝ × ℤ → ZigZag) ⁻¹' (Quotient.mk setoid '' W))
  have hsat : (Quotient.mk setoid : ℝ × ℤ → ZigZag) ⁻¹' (Quotient.mk setoid '' W) =
      W ∪ {b | ∃ a ∈ W, glued a b} ∪ {b | ∃ a ∈ W, glued b a} := by
    ext b
    simp only [Set.mem_preimage, Set.mem_image, Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨a, haW, ha⟩
      rcases Quotient.exact ha with rfl | h | h
      · exact .inl (.inl haW)
      · exact .inl (.inr ⟨a, haW, h⟩)
      · exact .inr ⟨a, haW, h⟩
    · rintro ((hbW | ⟨a, haW, h⟩) | ⟨a, haW, h⟩)
      · exact ⟨b, hbW, rfl⟩
      · exact ⟨a, haW, Quotient.sound (.inr (.inl h))⟩
      · exact ⟨a, haW, Quotient.sound (.inr (.inr h))⟩
  rw [hsat, partner_up_eq, partner_down_eq]
  refine IsOpen.union (IsOpen.union hW ?_) ?_
  · exact (hW.preimage (continuous_lineShift (-1))).inter (isOpen_setOf_glueAt (-1))
  · exact (hW.preimage (continuous_lineShift 1)).inter (isOpen_setOf_glueAt 0)
```
- The `n`-th sheet: the copy of `ℝ` given by line `n`. 
```lean
def sheet (n : ℤ) : ℝ → ZigZag := fun x ↦ mk x n

lemma continuous_sheet (n : ℤ) : Continuous (sheet n) :=
  continuous_mk.comp (continuous_id.prodMk continuous_const)

lemma sheet_injective (n : ℤ) : Function.Injective (sheet n) := by
  intro x y h
  rcases mk_eq_mk.mp h with h | h | h
  · exact congrArg Prod.fst h
  · exact absurd (congrArg Prod.snd h.1) (by simp)
  · exact absurd (congrArg Prod.snd h.1) (by simp)

lemma isOpenMap_sheet (n : ℤ) : IsOpenMap (sheet n) := by
  intro V hV
  have him : sheet n '' V = Quotient.mk setoid '' (V ×ˢ ({n} : Set ℤ)) := by
    ext b
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(x, n), ⟨hx, rfl⟩, rfl⟩
    · rintro ⟨⟨x, m⟩, ⟨hx, rfl⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
  rw [him]
  exact isOpenMap_mk _ (hV.prod (isOpen_discrete _))

lemma isOpenEmbedding_sheet (n : ℤ) : IsOpenEmbedding (sheet n) :=
  .of_continuous_injective_isOpenMap (continuous_sheet n) (sheet_injective n) (isOpenMap_sheet n)
```
! ### `p` is a quotient covering map for the ℤ-action 
```lean
lemma proj_even {x : ℝ} {n : ℤ} (h : Even n) : proj (x, n) = .inl x := if_pos h

lemma proj_odd {x : ℝ} {n : ℤ} (h : Odd n) : proj (x, n) = .inr x :=
  if_neg (Int.not_even_iff_odd.mpr h)

lemma surjective_proj : Function.Surjective proj := by
  rintro (x | x)
  · exact ⟨(x, 0), proj_even ⟨0, by ring⟩⟩
  · exact ⟨(x, 1), proj_odd ⟨0, by ring⟩⟩

lemma isOpenMap_proj : IsOpenMap proj := by
  intro W hW
  have him : proj '' W = Sum.inl '' {x | ∃ n, Even n ∧ (x, n) ∈ W} ∪
      Sum.inr '' {x | ∃ n, Odd n ∧ (x, n) ∈ W} := by
    ext s
    constructor
    · rintro ⟨⟨x, n⟩, hxn, rfl⟩
      rcases Int.even_or_odd n with he | ho
      · exact .inl ⟨x, ⟨n, he, hxn⟩, (proj_even he).symm⟩
      · exact .inr ⟨x, ⟨n, ho, hxn⟩, (proj_odd ho).symm⟩
    · rintro (⟨x, ⟨n, he, hxn⟩, rfl⟩ | ⟨x, ⟨n, ho, hxn⟩, rfl⟩)
      · exact ⟨(x, n), hxn, proj_even he⟩
      · exact ⟨(x, n), hxn, proj_odd ho⟩
  have hsec : ∀ (P : ℤ → Prop), IsOpen {x : ℝ | ∃ n, P n ∧ (x, n) ∈ W} := by
    intro P
    have : {x : ℝ | ∃ n, P n ∧ (x, n) ∈ W} = ⋃ n ∈ {n | P n}, {x | (x, n) ∈ W} := by
      ext s
      simp
    rw [this]
    exact isOpen_biUnion fun n _ ↦ hW.preimage (continuous_id.prodMk continuous_const)
  rw [him]
  exact (isOpenMap_inl _ (hsec _)).union (isOpenMap_inr _ (hsec _))

lemma isQuotientMap_p : IsQuotientMap p := by
  have hproj : IsQuotientMap proj := isOpenMap_proj.isQuotientMap continuous_proj surjective_proj
  have hq : IsQuotientMap (TwoOrigins.q ∘ proj) :=
    IsQuotientMap.comp (isQuotientMap_quotient_mk' : IsQuotientMap TwoOrigins.q) hproj
  have hcomp : IsQuotientMap (p ∘ (Quotient.mk setoid : ℝ × ℤ → ZigZag)) := hq
  exact IsQuotientMap.of_comp_isQuotientMap isQuotientMap_quotient_mk' hcomp

instance : ContinuousConstVAdd ℤ ZigZag where
  continuous_const_vadd k := by
    have h : Continuous ((fun e : ZigZag ↦ k +ᵥ e) ∘ (Quotient.mk setoid : ℝ × ℤ → ZigZag)) := by
      change Continuous fun a : ℝ × ℤ ↦ (Quotient.mk setoid (a.1, a.2 + 2 * k) : ZigZag)
      exact continuous_mk.comp (continuous_lineShift (2 * k))
    exact isQuotientMap_quotient_mk'.continuous_iff.mpr h
```
- Adjacent lines agree in `ZigZag` on their glued half. 
```lean
lemma mk_succ_eq {x : ℝ} {n : ℤ} (hg : glueAt n x) : mk x (n + 1) = mk x n :=
  Quotient.sound (.inr (.inr ⟨rfl, hg⟩))

lemma q_proj_eq_iff {x y : ℝ} {n m : ℤ} :
    TwoOrigins.q (proj (x, n)) = TwoOrigins.q (proj (y, m)) ↔
      x = y ∧ (n % 2 = m % 2 ∨ x ≠ 0) := by
  constructor
  · intro h
    have hrel : TwoR.rel (proj (x, n)) (proj (y, m)) := Quotient.exact h
    rcases Int.even_or_odd n with hn | hn <;> rcases Int.even_or_odd m with hm | hm
    · rw [proj_even hn, proj_even hm] at hrel
      rcases hrel with heq | ⟨hval, h0⟩
      · refine ⟨by injection heq, .inl ?_⟩
        rw [Int.even_iff] at hn hm
        omega
      · exact ⟨hval, .inr h0⟩
    · rw [proj_even hn, proj_odd hm] at hrel
      rcases hrel with heq | ⟨hval, h0⟩
      · exact absurd heq (by simp)
      · exact ⟨hval, .inr h0⟩
    · rw [proj_odd hn, proj_even hm] at hrel
      rcases hrel with heq | ⟨hval, h0⟩
      · exact absurd heq (by simp)
      · exact ⟨hval, .inr h0⟩
    · rw [proj_odd hn, proj_odd hm] at hrel
      rcases hrel with heq | ⟨hval, h0⟩
      · refine ⟨by injection heq, .inl ?_⟩
        rw [Int.odd_iff] at hn hm
        omega
      · exact ⟨hval, .inr h0⟩
  · rintro ⟨rfl, hpm⟩
    rcases Int.even_or_odd n with hn | hn <;> rcases Int.even_or_odd m with hm | hm
    · rw [proj_even hn, proj_even hm]
    · rw [proj_even hn, proj_odd hm]
      have hx0 : x ≠ 0 := by
        rcases hpm with hp | hp
        · rw [Int.even_iff] at hn
          rw [Int.odd_iff] at hm
          omega
        · exact hp
      exact TwoOrigins.glue hx0
    · rw [proj_odd hn, proj_even hm]
      have hx0 : x ≠ 0 := by
        rcases hpm with hp | hp
        · rw [Int.odd_iff] at hn
          rw [Int.even_iff] at hm
          omega
        · exact hp
      exact (TwoOrigins.glue hx0).symm
    · rw [proj_odd hn, proj_odd hm]

lemma mem_orbit_iff {x y : ℝ} {n m : ℤ} :
    mk x n ∈ AddAction.orbit ℤ (mk y m) ↔ x = y ∧ (n % 2 = m % 2 ∨ x ≠ 0) := by
  constructor
  · rintro ⟨k, hk⟩
    replace hk : k +ᵥ mk y m = mk x n := hk
    rw [vadd_mk] at hk
    rcases mk_eq_mk.mp hk with heq | hg | hg
    · injection heq with h1 h2
      exact ⟨h1.symm, .inl (by omega)⟩
    · obtain ⟨heq, hga⟩ := hg
      injection heq with h1 h2
      exact ⟨h1, .inr (h1 ▸ hga.ne_zero)⟩
    · obtain ⟨heq, hga⟩ := hg
      injection heq with h1 h2
      exact ⟨h1.symm, .inr hga.ne_zero⟩
  · rintro ⟨rfl, hpm⟩
    by_cases hpar : n % 2 = m % 2
    · refine ⟨(n - m) / 2, ?_⟩
      change (n - m) / 2 +ᵥ mk x m = mk x n
      rw [vadd_mk]
      congr 1
      omega
    · have hx0 : x ≠ 0 := hpm.resolve_left hpar
      rcases lt_or_gt_of_ne hx0 with hneg | hpos
      · rcases Int.even_or_odd n with hn | hn
        · refine ⟨(n - 1 - m) / 2, ?_⟩
          change (n - 1 - m) / 2 +ᵥ mk x m = mk x n
          rw [vadd_mk, show m + 2 * ((n - 1 - m) / 2) = n - 1 by
            rw [Int.even_iff] at hn; omega]
          have h := mk_succ_eq (x := x) (n := n - 1)
            (.inr ⟨by rw [Int.odd_iff]; rw [Int.even_iff] at hn; omega, hneg⟩)
          rw [show n - 1 + 1 = n by omega] at h
          exact h.symm
        · refine ⟨(n + 1 - m) / 2, ?_⟩
          change (n + 1 - m) / 2 +ᵥ mk x m = mk x n
          rw [vadd_mk, show m + 2 * ((n + 1 - m) / 2) = n + 1 by
            rw [Int.odd_iff] at hn; omega]
          exact mk_succ_eq (.inr ⟨hn, hneg⟩)
      · rcases Int.even_or_odd n with hn | hn
        · refine ⟨(n + 1 - m) / 2, ?_⟩
          change (n + 1 - m) / 2 +ᵥ mk x m = mk x n
          rw [vadd_mk, show m + 2 * ((n + 1 - m) / 2) = n + 1 by
            rw [Int.even_iff] at hn; omega]
          exact mk_succ_eq (.inl ⟨hn, hpos⟩)
        · refine ⟨(n - 1 - m) / 2, ?_⟩
          change (n - 1 - m) / 2 +ᵥ mk x m = mk x n
          rw [vadd_mk, show m + 2 * ((n - 1 - m) / 2) = n - 1 by
            rw [Int.odd_iff] at hn; omega]
          have h := mk_succ_eq (x := x) (n := n - 1)
            (.inl ⟨by rw [Int.even_iff]; rw [Int.odd_iff] at hn; omega, hpos⟩)
          rw [show n - 1 + 1 = n by omega] at h
          exact h.symm

lemma p_eq_p_iff {e₁ e₂ : ZigZag} : p e₁ = p e₂ ↔ e₁ ∈ AddAction.orbit ℤ e₂ := by
  obtain ⟨⟨x, n⟩⟩ := e₁
  obtain ⟨⟨y, m⟩⟩ := e₂
  exact q_proj_eq_iff.trans mem_orbit_iff.symm

lemma disjoint_translates (e : ZigZag) :
    ∃ U ∈ 𝓝 e, ∀ g : ℤ, ((g +ᵥ ·) '' U ∩ U).Nonempty → g = 0 := by
  obtain ⟨⟨x₀, n₀⟩⟩ := e
  refine ⟨Set.range (sheet n₀), (isOpenMap_sheet n₀).isOpen_range.mem_nhds ⟨x₀, rfl⟩, ?_⟩
  rintro g ⟨u, ⟨v, ⟨y, rfl⟩, rfl⟩, x, hx⟩
  have h : mk x n₀ = mk y (n₀ + 2 * g) := by
    rw [← vadd_mk]
    exact hx
  rcases mk_eq_mk.mp h with heq | hg | hg
  · injection heq with h1 h2
    omega
  · injection hg.1 with h1 h2
    omega
  · injection hg.1 with h1 h2
    omega
```
- The zigzag is a quotient covering of the line with two origins for the shift action of ℤ. 
```lean
theorem isAddQuotientCoveringMap_p : IsAddQuotientCoveringMap p ℤ where
  __ := isQuotientMap_p
  __ := (inferInstance : ContinuousConstVAdd ℤ ZigZag)
  apply_eq_iff_mem_orbit := p_eq_p_iff
  disjoint := disjoint_translates

end ZigZag
```

License
===

Copyright (C) 2025  Eric Klavins

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.   

