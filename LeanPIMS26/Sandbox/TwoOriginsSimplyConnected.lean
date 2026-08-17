import LeanPIMS26.Sandbox.TwoOriginsCover

open Topology

namespace ZigZag

/-! ### The coordinate function -/

/-- The real coordinate of a point of `ZigZag`; well-defined since glued pairs share it. -/
def val : ZigZag → ℝ := Quotient.lift Prod.fst fun a b h ↦ by
  rcases h with rfl | h | h
  · rfl
  · rw [h.1]
  · rw [h.1]

lemma val_mk (x : ℝ) (n : ℤ) : val (mk x n) = x := rfl

lemma continuous_val : Continuous val := by
  have h : Continuous (val ∘ (Quotient.mk setoid : ℝ × ℤ → ZigZag)) := continuous_fst
  exact isQuotientMap_quotient_mk'.continuous_iff.mpr h

lemma coord_eq_of_mk_eq {x y : ℝ} {n m : ℤ} (h : mk x n = mk y m) : x = y := congrArg val h

/-! ### Points are closed -/

lemma isClosed_singleton (e : ZigZag) : IsClosed {e} := by
  obtain ⟨⟨x, n⟩⟩ := e
  have hpre : IsClosed ((Quotient.mk setoid : ℝ × ℤ → ZigZag) ⁻¹'
      {(Quotient.mk setoid (x, n) : ZigZag)}) := by
    refine Set.Finite.isClosed (Set.Finite.subset
      (((Set.finite_singleton (x, n + 1)).insert (x, n)).insert (x, n - 1)) ?_)
    rintro a ha
    have h : rel a (x, n) := Quotient.exact ha
    rcases h with rfl | h | h
    · simp
    · have heq : (x, n) = (a.1, a.2 + 1) := h.1
      injection heq with h1 h2
      left
      exact Prod.ext h1.symm (by omega)
    · rw [h.1]
      simp
  exact isQuotientMap_quotient_mk'.isClosed_preimage.mp hpre

instance : T1Space ZigZag := ⟨isClosed_singleton⟩

/-! ### Membership in sheet images -/

lemma mem_sheet_image {B : Set ℝ} {x : ℝ} {n j : ℤ} :
    mk x n ∈ sheet j '' B ↔ x ∈ B ∧ mk x j = mk x n := by
  constructor
  · rintro ⟨w, hwB, hw⟩
    obtain rfl : w = x := coord_eq_of_mk_eq hw
    exact ⟨hwB, hw⟩
  · rintro ⟨hB, h⟩
    exact ⟨x, hB, h⟩

/-- When do two points with the same coordinate on different lines coincide? -/
lemma mk_line_eq_iff {x : ℝ} {n j : ℤ} :
    mk x j = mk x n ↔ j = n ∨ (n = j + 1 ∧ glueAt j x) ∨ (j = n + 1 ∧ glueAt n x) := by
  rw [mk_eq_mk]
  constructor
  · rintro (heq | h | h)
    · exact .inl (by injection heq with h1 h2)
    · refine .inr (.inl ⟨?_, h.2⟩)
      have := h.1
      injection this with h1 h2
    · refine .inr (.inr ⟨?_, h.2⟩)
      have := h.1
      injection this with h1 h2
  · rintro (rfl | ⟨rfl, hg⟩ | ⟨rfl, hg⟩)
    · exact .inl rfl
    · exact .inr (.inl ⟨rfl, hg⟩)
    · exact .inr (.inr ⟨rfl, hg⟩)

/-! ### Chains of lines -/

/-- The union of the sheets with index in `[a, b]`. -/
def chain (a b : ℤ) : Set ZigZag := ⋃ j ∈ Set.Icc a b, Set.range (sheet j)

lemma isOpen_chain (a b : ℤ) : IsOpen (chain a b) :=
  isOpen_biUnion fun j _ ↦ (isOpenMap_sheet j).isOpen_range

lemma mem_chain_iff {e : ZigZag} {a b : ℤ} :
    e ∈ chain a b ↔ ∃ j, a ≤ j ∧ j ≤ b ∧ ∃ x, mk x j = e := by
  simp only [chain, Set.mem_iUnion, Set.mem_range, Set.mem_Icc, sheet]
  constructor
  · rintro ⟨j, ⟨h1, h2⟩, x, hx⟩
    exact ⟨j, h1, h2, x, hx⟩
  · rintro ⟨j, h1, h2, x, hx⟩
    exact ⟨j, ⟨h1, h2⟩, x, hx⟩

lemma chain_mono {a b a' b' : ℤ} (ha : a' ≤ a) (hb : b ≤ b') : chain a b ⊆ chain a' b' := by
  intro e he
  rw [mem_chain_iff] at he ⊢
  obtain ⟨j, h1, h2, hx⟩ := he
  exact ⟨j, by omega, by omega, hx⟩

lemma mk_mem_chain {x : ℝ} {j a b : ℤ} (h1 : a ≤ j) (h2 : j ≤ b) : mk x j ∈ chain a b :=
  mem_chain_iff.mpr ⟨j, h1, h2, x, rfl⟩

/-! ### Path-connectedness -/

lemma joined_on_sheet (n : ℤ) (x y : ℝ) : Joined (mk x n) (mk y n) := by
  refine ⟨⟨⟨fun t ↦ mk ((1 - t) * x + t * y) n, ?_⟩, ?_, ?_⟩⟩
  · exact (continuous_sheet n).comp (by fun_prop)
  · simp
  · simp

/-- The coordinate of the glued half of the junction `(n, n+1)`. -/
noncomputable def side (n : ℤ) : ℝ := if Even n then 1 else -1

lemma glueAt_side (n : ℤ) : glueAt n (side n) := by
  rcases Int.even_or_odd n with he | ho
  · exact .inl ⟨he, by simp [side, he]⟩
  · refine .inr ⟨ho, ?_⟩
    rw [side, if_neg (Int.not_even_iff_odd.mpr ho)]
    norm_num

lemma joined_to_base (e : ZigZag) : Joined e (mk 0 0) := by
  obtain ⟨⟨x, n⟩⟩ := e
  change Joined (mk x n) (mk 0 0)
  induction n using Int.induction_on generalizing x with
  | zero => exact joined_on_sheet 0 x 0
  | succ i ih =>
    refine (joined_on_sheet _ x (side i)).trans ?_
    rw [mk_succ_eq (glueAt_side i)]
    exact ih _
  | pred i ih =>
    refine (joined_on_sheet _ x (side (-i - 1))).trans ?_
    have h := mk_succ_eq (x := side (-i - 1)) (glueAt_side (-i - 1))
    rw [show (-(i : ℤ) - 1 + 1 : ℤ) = -i by omega] at h
    rw [← h]
    exact ih _

instance : PathConnectedSpace ZigZag where
  nonempty := ⟨mk 0 0⟩
  joined x y := (joined_to_base x).trans (joined_to_base y).symm

/-! ### The glued side of a junction, via signs -/

lemma side_eq_one_or_neg_one (n : ℤ) : side n = 1 ∨ side n = -1 := by
  unfold side
  split <;> simp

lemma glueAt_iff_side {n : ℤ} {x : ℝ} : glueAt n x ↔ 0 < side n * x := by
  rcases Int.even_or_odd n with he | ho
  · rw [side, if_pos he, one_mul]
    constructor
    · rintro (⟨-, h⟩ | ⟨ho, -⟩)
      · exact h
      · exact absurd he (Int.not_even_iff_odd.mpr ho)
    · exact fun h ↦ .inl ⟨he, h⟩
  · rw [side, if_neg (Int.not_even_iff_odd.mpr ho)]
    constructor
    · rintro (⟨he, -⟩ | ⟨-, h⟩)
      · exact absurd he (Int.not_even_iff_odd.mpr ho)
      · linarith
    · intro h
      exact .inr ⟨ho, by linarith⟩

/-- Crossing the junction `(j, j+1)` on its glued side. -/
lemma glue_across {j : ℤ} {w : ℝ} (h : 0 < side j * w) : mk w (j + 1) = mk w j :=
  mk_succ_eq (glueAt_iff_side.mpr h)

/-! ### The reflection symmetry `(x, n) ↦ (-x, -n)` -/

/-- Reflection of the underlying data. -/
def reflFun (a : ℝ × ℤ) : ℝ × ℤ := (-a.1, -a.2)

lemma glueAt_reflected {n : ℤ} {x : ℝ} (h : glueAt n x) : glueAt (-n - 1) (-x) := by
  rcases h with ⟨he, hx⟩ | ⟨ho, hx⟩
  · refine .inr ⟨?_, by linarith⟩
    rw [Int.odd_iff]
    rw [Int.even_iff] at he
    omega
  · refine .inl ⟨?_, by linarith⟩
    rw [Int.even_iff]
    rw [Int.odd_iff] at ho
    omega

lemma glued_reflFun {a b : ℝ × ℤ} (h : glued a b) : glued (reflFun b) (reflFun a) := by
  obtain ⟨rfl, hg⟩ := h
  refine ⟨Prod.ext rfl ?_, ?_⟩
  · change -a.2 = -(a.2 + 1) + 1
    ring
  · change glueAt (-(a.2 + 1)) (-a.1)
    rw [show (-(a.2 + 1) : ℤ) = -a.2 - 1 by ring]
    exact glueAt_reflected hg

lemma rel_reflFun {a b : ℝ × ℤ} (h : rel a b) : rel (reflFun a) (reflFun b) := by
  rcases h with rfl | h | h
  · exact .inl rfl
  · exact .inr (.inr (glued_reflFun h))
  · exact .inr (.inl (glued_reflFun h))

/-- Reflection of the zigzag. -/
def reflZ : ZigZag → ZigZag := Quotient.map reflFun fun _ _ ↦ rel_reflFun

lemma reflZ_mk (x : ℝ) (n : ℤ) : reflZ (mk x n) = mk (-x) (-n) := rfl

lemma reflZ_reflZ (e : ZigZag) : reflZ (reflZ e) = e := by
  obtain ⟨⟨x, n⟩⟩ := e
  exact congrArg (Quotient.mk setoid) (by simp [reflFun])

lemma continuous_reflZ : Continuous reflZ := by
  have h : Continuous (reflZ ∘ (Quotient.mk setoid : ℝ × ℤ → ZigZag)) := by
    change Continuous fun a : ℝ × ℤ ↦ (Quotient.mk setoid (reflFun a) : ZigZag)
    refine continuous_mk.comp ?_
    exact (continuous_fst.neg).prodMk
      ((continuous_of_discreteTopology (f := fun n : ℤ ↦ -n)).comp continuous_snd)
  exact isQuotientMap_quotient_mk'.continuous_iff.mpr h

/-- Reflection as a homeomorphism of the zigzag. -/
def R : ZigZag ≃ₜ ZigZag where
  toFun := reflZ
  invFun := reflZ
  left_inv := reflZ_reflZ
  right_inv := reflZ_reflZ
  continuous_toFun := continuous_reflZ
  continuous_invFun := continuous_reflZ

lemma reflZ_base : reflZ (mk 0 0) = mk 0 0 := by
  rw [reflZ_mk]
  norm_num

lemma reflZ_mem_chain {e : ZigZag} {a b : ℤ} (h : e ∈ chain a b) :
    reflZ e ∈ chain (-b) (-a) := by
  rw [mem_chain_iff] at h ⊢
  obtain ⟨j, h1, h2, x, hx⟩ := h
  exact ⟨-j, by omega, by omega, -x, by rw [← hx, reflZ_mk]⟩

/-! ### Sheet-interval neighborhood basis -/

lemma exists_sheet_ball_subset {U : Set ZigZag} (hU : IsOpen U) {x : ℝ} {n : ℤ}
    (hx : mk x n ∈ U) : ∃ δ > 0, sheet n '' Metric.ball x δ ⊆ U := by
  have hpre : IsOpen ((Quotient.mk setoid : ℝ × ℤ → ZigZag) ⁻¹' U) := hU.preimage continuous_mk
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hpre (x, n) hx
  refine ⟨δ, hδ, ?_⟩
  rintro e ⟨y, hy, rfl⟩
  refine hball ?_
  rw [Metric.mem_ball] at hy ⊢
  rw [Prod.dist_eq]
  simp only [dist_self]
  rw [max_eq_left dist_nonneg]
  exact hy

/-! ### The unshared half of the top line, and its interaction with chains -/

/-- The half of line `b` not glued to line `b - 1` (including the origin of line `b`). -/
def topBad (b : ℤ) : Set ZigZag := {e | ∃ x, side (b - 1) * x ≤ 0 ∧ e = mk x b}

lemma not_topBad_of_mem_lower {e : ZigZag} {a b : ℤ} (h : e ∈ chain a (b - 1)) :
    e ∉ topBad b := by
  rintro ⟨x, hx, rfl⟩
  rw [mem_chain_iff] at h
  obtain ⟨j, hj1, hj2, u, hu⟩ := h
  obtain rfl : u = x := coord_eq_of_mk_eq hu
  rcases mk_line_eq_iff.mp hu with rfl | ⟨hj, hg⟩ | ⟨hj, hg⟩
  · omega
  · rw [glueAt_iff_side] at hg
    have hj' : j = b - 1 := by omega
    subst hj'
    linarith
  · omega

lemma mem_topBad_iff {x : ℝ} {b : ℤ} : mk x b ∈ topBad b ↔ side (b - 1) * x ≤ 0 := by
  constructor
  · rintro ⟨y, hy, he⟩
    obtain rfl : x = y := coord_eq_of_mk_eq he
    exact hy
  · intro h
    exact ⟨x, h, rfl⟩

lemma mem_lower_of_not_topBad {e : ZigZag} {a b : ℤ} (ha : a ≤ 0) (hb : 1 ≤ b)
    (h : e ∈ chain a b) (h2 : e ∉ topBad b) : e ∈ chain a (b - 1) := by
  rw [mem_chain_iff] at h
  obtain ⟨j, hj1, hj2, u, hu⟩ := h
  rcases lt_or_eq_of_le hj2 with hlt | rfl
  · exact mem_chain_iff.mpr ⟨j, hj1, by omega, u, hu⟩
  · rw [← hu] at h2 ⊢
    rw [mem_topBad_iff, not_le] at h2
    have hg := glue_across h2
    rw [show j - 1 + 1 = j by omega] at hg
    rw [hg]
    exact mk_mem_chain (by omega) le_rfl

lemma not_mem_closure_lower {x : ℝ} {a b : ℤ} (hx : side (b - 1) * x < 0) :
    mk x b ∉ closure (chain a (b - 1)) := by
  have hopen : IsOpen (sheet b '' {y | side (b - 1) * y < 0}) :=
    isOpenMap_sheet b _ (isOpen_Iio.preimage (continuous_const.mul continuous_id))
  intro hmem
  obtain ⟨e, heO, heC⟩ := mem_closure_iff.mp hmem _ hopen ⟨x, hx, rfl⟩
  obtain ⟨y, hy, rfl⟩ := heO
  exact not_topBad_of_mem_lower heC ⟨y, le_of_lt hy, rfl⟩

/-! ### Reduction, part 1: fold the top line of a chain onto the line below -/

open unitInterval in
lemma fold_top {a b : ℤ} (ha : a ≤ 0) (hb : 1 ≤ b) (γ : Path (mk 0 0) (mk 0 0))
    (hγ : ∀ s, γ s ∈ chain a b) :
    ∃ γ₁ : Path (mk 0 0) (mk 0 0),
      (∀ s, γ₁ s ∈ chain a (b - 1) ∨ γ₁ s = mk 0 b) ∧ γ.Homotopic γ₁ := by
  classical
  set sg : ℝ := side (b - 1) with hsgdef
  set A : Set I := (γ ⁻¹' chain a (b - 1))ᶜ with hAdef
  have hAclosed : IsClosed A := ((isOpen_chain a (b - 1)).preimage γ.continuous).isClosed_compl
  have hAform : ∀ s ∈ A, γ s = mk (val (γ s)) b ∧ sg * val (γ s) ≤ 0 := by
    intro s hs
    have h1 : γ s ∈ topBad b := by
      by_contra h2
      exact hs (mem_lower_of_not_topBad ha hb (hγ s) h2)
    obtain ⟨x, hx, he⟩ := h1
    rw [he, val_mk]
    exact ⟨rfl, hx⟩
  have hsgpm : sg = 1 ∨ sg = -1 := side_eq_one_or_neg_one _
  have hsgsq : sg * sg = 1 := by rcases hsgpm with h | h <;> rw [h] <;> norm_num
  have hfr : ∀ s ∈ frontier A, γ s = mk 0 b := by
    intro s hs
    have hsA : s ∈ A := hAclosed.frontier_subset hs
    have hcl : γ s ∈ closure (chain a (b - 1)) := by
      have h1 : s ∈ closure Aᶜ := by
        rw [closure_compl]
        exact hs.2
      rw [hAdef, compl_compl] at h1
      exact γ.continuous.closure_preimage_subset _ h1
    obtain ⟨hform, hle⟩ := hAform s hsA
    rcases lt_or_eq_of_le hle with hlt | heq
    · rw [hform] at hcl
      exact absurd hcl (not_mem_closure_lower hlt)
    · have hval : val (γ s) = 0 := by
        rcases hsgpm with h | h <;> rw [h] at heq <;> linarith
      rw [hform, hval]
  set f : I × I → ZigZag :=
    fun q ↦ mk (val (γ q.2) - 2 * q.1 * sg * min (sg * val (γ q.2)) 0) b with hfdef
  have hfc : Continuous f := by
    refine (continuous_sheet b).comp ?_
    have hc : Continuous fun q : I × I ↦ val (γ q.2) :=
      continuous_val.comp (γ.continuous.comp continuous_snd)
    have ht : Continuous fun q : I × I ↦ (q.1 : ℝ) :=
      continuous_subtype_val.comp continuous_fst
    exact hc.sub (((continuous_const.mul ht).mul continuous_const).mul
      ((continuous_const.mul hc).min continuous_const))
  set F : I × I → ZigZag := (Set.univ ×ˢ A).piecewise f (fun q ↦ γ q.2) with hFdef
  have hF_mem : ∀ q : I × I, q.2 ∈ A → F q = f q := fun q hq ↦
    Set.piecewise_eq_of_mem _ _ _ (Set.mem_prod.mpr ⟨Set.mem_univ _, hq⟩)
  have hF_notmem : ∀ q : I × I, q.2 ∉ A → F q = γ q.2 := fun q hq ↦
    Set.piecewise_eq_of_notMem _ _ _ (fun h ↦ hq (Set.mem_prod.mp h).2)
  have hagree : ∀ q ∈ frontier (Set.univ ×ˢ A), f q = γ q.2 := by
    intro q hq
    rw [frontier_univ_prod_eq] at hq
    have h0 : γ q.2 = mk 0 b := hfr _ hq.2
    have hv : val (γ q.2) = 0 := by rw [h0]; rfl
    simp only [hfdef]
    rw [hv, h0, mul_zero, min_self, mul_zero, sub_zero]
  have hFcont : Continuous F :=
    Continuous.piecewise hagree hfc (γ.continuous.comp continuous_snd)
  have h0A : (0 : I) ∉ A := by
    intro h
    refine h ?_
    rw [Set.mem_preimage, γ.source]
    exact mk_mem_chain ha (by omega)
  have h1A : (1 : I) ∉ A := by
    intro h
    refine h ?_
    rw [Set.mem_preimage, γ.target]
    exact mk_mem_chain ha (by omega)
  refine ⟨⟨⟨fun s ↦ F (1, s), hFcont.comp (continuous_const.prodMk continuous_id)⟩, ?_, ?_⟩,
    ?_, ?_⟩
  · exact (hF_notmem (1, 0) h0A).trans γ.source
  · exact (hF_notmem (1, 1) h1A).trans γ.target
  · intro s
    by_cases hs : s ∈ A
    · obtain ⟨hform, hle⟩ := hAform s hs
      rcases lt_or_eq_of_le hle with hlt | heq
      · left
        change F (1, s) ∈ chain a (b - 1)
        rw [hF_mem (1, s) hs]
        change mk (val (γ s) - 2 * ((1 : I) : ℝ) * sg * min (sg * val (γ s)) 0) b ∈
          chain a (b - 1)
        rw [show ((1 : I) : ℝ) = 1 from rfl, min_eq_left hle,
          show val (γ s) - 2 * 1 * sg * (sg * val (γ s)) = -val (γ s) by
            linear_combination (-2 * val (γ s)) * hsgsq]
        have hpos : 0 < sg * -val (γ s) := by
          have h : sg * -val (γ s) = -(sg * val (γ s)) := by ring
          rw [h]
          linarith
        have hg := glue_across hpos
        rw [show b - 1 + 1 = b by omega] at hg
        rw [hg]
        exact mk_mem_chain (by omega) le_rfl
      · right
        change F (1, s) = mk 0 b
        rw [hF_mem (1, s) hs]
        have hval : val (γ s) = 0 := by
          rcases hsgpm with h | h <;> rw [h] at heq <;> linarith
        change mk (val (γ s) - 2 * ((1 : I) : ℝ) * sg * min (sg * val (γ s)) 0) b = mk 0 b
        rw [hval, mul_zero, min_self, mul_zero, sub_zero]
    · left
      change F (1, s) ∈ chain a (b - 1)
      rw [hF_notmem (1, s) hs]
      exact not_not.mp hs
  · refine ⟨⟨⟨⟨F, hFcont⟩, ?_, fun s ↦ rfl⟩, ?_⟩⟩
    · intro s
      by_cases hs : s ∈ A
      · refine (hF_mem (0, s) hs).trans ?_
        change mk (val (γ s) - 2 * ((0 : I) : ℝ) * sg * min (sg * val (γ s)) 0) b = γ s
        rw [show ((0 : I) : ℝ) = 0 from rfl, mul_zero, zero_mul, zero_mul, sub_zero]
        exact ((hAform s hs).1).symm
      · exact hF_notmem (0, s) hs
    · intro t s hs
      rcases hs with rfl | hs
      · exact hF_notmem (t, 0) h0A
      · rw [Set.mem_singleton_iff] at hs
        subst hs
        exact hF_notmem (t, 1) h1A

/-! ### Reduction, part 2: swap the stranded top origin down to the line below -/

open unitInterval in
lemma swap_top {a b : ℤ} (ha : a ≤ 0) (hb : 1 ≤ b) (γ₁ : Path (mk 0 0) (mk 0 0))
    (hγ₁ : ∀ s, γ₁ s ∈ chain a (b - 1) ∨ γ₁ s = mk 0 b) :
    ∃ γ₂ : Path (mk 0 0) (mk 0 0), (∀ s, γ₂ s ∈ chain a (b - 1)) ∧ γ₁.Homotopic γ₂ := by
  classical
  set sg : ℝ := side (b - 1) with hsgdef
  have hsgpm : sg = 1 ∨ sg = -1 := side_eq_one_or_neg_one _
  have hsgsq : sg * sg = 1 := by rcases hsgpm with h | h <;> rw [h] <;> norm_num
  set K : Set I := γ₁ ⁻¹' {mk 0 b} with hKdef
  have hKclosed : IsClosed K := (isClosed_singleton _).preimage γ₁.continuous
  have hK_iff : ∀ s : I, s ∈ K ↔ γ₁ s = mk 0 b := fun s ↦ Iff.rfl
  set V : Set I := γ₁ ⁻¹' (sheet b '' Metric.ball 0 1) with hVdef
  have hVopen : IsOpen V :=
    ((isOpenMap_sheet b _ Metric.isOpen_ball).preimage γ₁.continuous)
  have hKV : K ⊆ V := by
    intro s hs
    rw [hVdef, Set.mem_preimage, (hK_iff s).mp hs]
    exact ⟨0, Metric.mem_ball_self one_pos, rfl⟩
  have hbase_ne : mk 0 0 ∉ sheet b '' Metric.ball 0 1 := by
    intro h
    rw [mem_sheet_image] at h
    rcases mk_line_eq_iff.mp h.2 with h3 | ⟨h3, hg⟩ | ⟨h3, hg⟩
    · omega
    · exact hg.ne_zero rfl
    · exact hg.ne_zero rfl
  have h0V : (0 : I) ∉ V := by
    intro h
    rw [hVdef, Set.mem_preimage, γ₁.source] at h
    exact hbase_ne h
  have h1V : (1 : I) ∉ V := by
    intro h
    rw [hVdef, Set.mem_preimage, γ₁.target] at h
    exact hbase_ne h
  have hcK : ∀ s ∈ K, val (γ₁ s) = 0 := by
    intro s hs
    rw [(hK_iff s).mp hs]
    rfl
  have hS1 : ∀ s ∈ V, s ∉ K → γ₁ s = mk (val (γ₁ s)) (b - 1) ∧ 0 < sg * val (γ₁ s) := by
    intro s hsV hsK
    rw [hVdef, Set.mem_preimage] at hsV
    obtain ⟨y, hy, hey⟩ := hsV
    have hyval : val (γ₁ s) = y := by rw [← hey]; rfl
    rcases hγ₁ s with hch | hal
    · rw [← hey] at hch
      have hnb : sheet b y ∉ topBad b := not_topBad_of_mem_lower hch
      have hpos : 0 < sg * y := by
        by_contra h
        exact hnb (mem_topBad_iff.mpr (by linarith [not_lt.mp h]))
      have hg := glue_across hpos
      rw [show b - 1 + 1 = b by omega] at hg
      refine ⟨?_, by rw [hyval]; exact hpos⟩
      rw [hyval, ← hey]
      exact hg
    · exact absurd ((hK_iff s).mpr hal) hsK
  have hfrV : ∀ s ∈ frontier V, s ∉ V := fun s hs h ↦ hs.2 (by rwa [hVopen.interior_eq])
  have hS3core : ∀ e, e ∈ chain a (b - 1) → e ∈ closure (sheet b '' Metric.ball 0 1) →
      e = mk (val e) (b - 1) := by
    intro e hch hcl
    by_cases hform : ∃ u, e = mk u (b - 1)
    · obtain ⟨u, rfl⟩ := hform
      rw [val_mk]
    · exfalso
      rw [mem_chain_iff] at hch
      obtain ⟨j, hj1, hj2, u, hu⟩ := hch
      have hj : j ≤ b - 2 := by
        rcases lt_or_eq_of_le hj2 with h | rfl
        · omega
        · exact absurd ⟨u, hu.symm⟩ hform
      obtain ⟨e', he'O, he'S⟩ := mem_closure_iff.mp hcl (Set.range (sheet j))
        (isOpenMap_sheet j).isOpen_range ⟨u, hu⟩
      obtain ⟨w', hw'⟩ := he'O
      obtain ⟨y, hy, hey⟩ := he'S
      have heq : mk y b = mk w' j := hey.trans hw'.symm
      obtain rfl : y = w' := coord_eq_of_mk_eq heq
      rcases mk_line_eq_iff.mp heq with h3 | ⟨h3, -⟩ | ⟨h3, -⟩ <;> omega
  have hS3 : ∀ s ∈ frontier V, γ₁ s = mk (val (γ₁ s)) (b - 1) := by
    intro s hs
    have hsV : s ∉ V := hfrV s hs
    have hsK : s ∉ K := fun h ↦ hsV (hKV h)
    have hch : γ₁ s ∈ chain a (b - 1) := (hγ₁ s).resolve_right fun h ↦ hsK ((hK_iff s).mpr h)
    have hcl : γ₁ s ∈ closure (sheet b '' Metric.ball 0 1) := by
      have h1 : s ∈ closure V := hs.1
      rw [hVdef] at h1
      exact γ₁.continuous.closure_preimage_subset _ h1
    exact hS3core _ hch hcl
  -- the bump size
  set w : I → ℝ := fun s ↦ Metric.infDist s Vᶜ with hwdef
  have hVc_ne : Vᶜ.Nonempty := ⟨0, h0V⟩
  have hwcont : Continuous w := Metric.continuous_infDist_pt _
  have hw0 : ∀ s ∉ V, w s = 0 := fun s hs ↦ Metric.infDist_zero_of_mem hs
  have hwpos : ∀ s ∈ V, 0 < w s := by
    intro s hs
    change 0 < Metric.infDist s Vᶜ
    refine (Metric.infDist_pos_iff_notMem_closure hVc_ne).mp ?_
    rw [hVopen.isClosed_compl.closure_eq]
    exact fun h ↦ h hs
  have hwle1 : ∀ s, w s ≤ 1 := by
    intro s
    refine (Metric.infDist_le_dist_of_mem h0V).trans ?_
    rw [Subtype.dist_eq, Real.dist_eq, show (((0 : I) : ℝ)) = 0 from rfl, sub_zero,
      abs_of_nonneg s.2.1]
    exact s.2.2
  -- the pushed map
  set Q : I × I → ZigZag := (Set.univ ×ˢ V).piecewise
    (fun q ↦ mk (val (γ₁ q.2) + sg * (q.1 * (1 - q.1) * w q.2)) (b - 1))
    (fun q ↦ γ₁ q.2) with hQdef
  have hQ_mem : ∀ q : I × I, q.2 ∈ V →
      Q q = mk (val (γ₁ q.2) + sg * (q.1 * (1 - q.1) * w q.2)) (b - 1) := fun q hq ↦
    Set.piecewise_eq_of_mem _ _ _ (Set.mem_prod.mpr ⟨Set.mem_univ _, hq⟩)
  have hQ_notmem : ∀ q : I × I, q.2 ∉ V → Q q = γ₁ q.2 := fun q hq ↦
    Set.piecewise_eq_of_notMem _ _ _ (fun h ↦ hq (Set.mem_prod.mp h).2)
  have hQcont : Continuous Q := by
    refine Continuous.piecewise ?_ ?_ (γ₁.continuous.comp continuous_snd)
    · intro q hq
      rw [frontier_univ_prod_eq] at hq
      have hfr := hS3 _ hq.2
      have hw' : w q.2 = 0 := hw0 _ (hfrV _ hq.2)
      rw [hw', mul_zero, mul_zero, add_zero]
      exact hfr.symm
    · refine (continuous_sheet (b - 1)).comp ?_
      have hc : Continuous fun q : I × I ↦ val (γ₁ q.2) :=
        continuous_val.comp (γ₁.continuous.comp continuous_snd)
      have ht : Continuous fun q : I × I ↦ (q.1 : ℝ) :=
        continuous_subtype_val.comp continuous_fst
      have hwq : Continuous fun q : I × I ↦ w q.2 := hwcont.comp continuous_snd
      exact hc.add (continuous_const.mul ((ht.mul (continuous_const.sub ht)).mul hwq))
  -- the homotopy map with the special time-zero slice
  set H : I × I → ZigZag := fun q ↦ if q.1 = 0 then γ₁ q.2 else Q q with hHdef
  have hHQ : ∀ q : I × I, q.2 ∉ K → H q = Q q := by
    intro q hq
    change (if q.1 = 0 then γ₁ q.2 else Q q) = Q q
    split_ifs with ht
    · by_cases hv : q.2 ∈ V
      · rw [hQ_mem _ hv, ht, show ((0 : I) : ℝ) = 0 from rfl, zero_mul, zero_mul, mul_zero,
          add_zero]
        exact (hS1 _ hv hq).1
      · rw [hQ_notmem _ hv]
    · rfl
  have hIone_ne : (1 : I) ≠ 0 := fun h ↦ one_ne_zero (congrArg Subtype.val h)
  have hHcont : Continuous H := by
    rw [continuous_iff_continuousAt]
    intro q
    by_cases hq : q.1 = 0 ∧ q.2 ∈ K
    · obtain ⟨ht0, hsK⟩ := hq
      have hval0 : H q = mk 0 b := by
        rw [hHdef]
        simp only [if_pos ht0]
        exact (hK_iff q.2).mp hsK
      rw [ContinuousAt, hval0, Filter.tendsto_def]
      intro U hU
      obtain ⟨U', hU'sub, hU'open, hU'mem⟩ := mem_nhds_iff.mp hU
      obtain ⟨δ', hδ', hδ'sub⟩ := exists_sheet_ball_subset hU'open hU'mem
      set δ : ℝ := min δ' 1 with hδdef
      have hδpos : 0 < δ := lt_min hδ' one_pos
      have hδle1 : δ ≤ 1 := min_le_right _ _
      have hδleδ' : δ ≤ δ' := min_le_left _ _
      set J : Set I := γ₁ ⁻¹' (sheet b '' Metric.ball 0 (δ / 2)) with hJdef
      have hJopen : IsOpen J := (isOpenMap_sheet b _ Metric.isOpen_ball).preimage γ₁.continuous
      have hsJ : q.2 ∈ J := by
        rw [hJdef, Set.mem_preimage, (hK_iff q.2).mp hsK]
        exact ⟨0, Metric.mem_ball_self (by positivity), rfl⟩
      set T : Set I := (fun t : I ↦ (t : ℝ)) ⁻¹' Set.Iio (δ / 2) with hTdef
      have hTopen : IsOpen T := isOpen_Iio.preimage continuous_subtype_val
      have h0T : q.1 ∈ T := by
        rw [hTdef, Set.mem_preimage, ht0]
        show ((0 : I) : ℝ) ∈ Set.Iio (δ / 2)
        rw [show ((0 : I) : ℝ) = 0 from rfl]
        exact Set.mem_Iio.mpr (by positivity)
      have hmain : T ×ˢ J ⊆ H ⁻¹' U := by
        rintro ⟨t, s⟩ ⟨htT, hsJ'⟩
        rw [hTdef, Set.mem_preimage, Set.mem_Iio] at htT
        rw [hJdef, Set.mem_preimage] at hsJ'
        obtain ⟨y, hy, hey⟩ := hsJ'
        rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hy
        have hyval : val (γ₁ s) = y := by rw [← hey]; rfl
        have hsV : s ∈ V := by
          rw [hVdef, Set.mem_preimage]
          exact ⟨y, Metric.mem_ball.mpr (by rw [Real.dist_eq, sub_zero]; linarith), hey⟩
        rw [Set.mem_preimage]
        by_cases ht : t = 0
        · rw [hHdef]
          simp only [ht]
          refine hU'sub (hδ'sub ?_)
          exact ⟨y, Metric.mem_ball.mpr (by rw [Real.dist_eq, sub_zero]; linarith), hey⟩
        · rw [hHdef]
          simp only [if_neg ht]
          rw [hQ_mem _ hsV]
          have htReal_ne : (t : ℝ) ≠ 0 := fun h ↦ ht (Subtype.ext h)
          have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.2.1 (Ne.symm htReal_ne)
          have ht1 : (t : ℝ) ≤ 1 := t.2.2
          have h1mt : 0 < 1 - (t : ℝ) := by
            have : (t : ℝ) < 1 := by linarith [htT, hδle1]
            linarith
          have hwpos' := hwpos s hsV
          have hwle := hwle1 s
          have htw_nonneg : 0 ≤ (t : ℝ) * (1 - t) * w s :=
            mul_nonneg (mul_nonneg htpos.le h1mt.le) hwpos'.le
          have htT' : (t : ℝ) < δ / 2 := htT
          have htw_lt : (t : ℝ) * (1 - t) * w s < δ / 2 := by
            have h1 : (t : ℝ) * (1 - t) * w s ≤ (t : ℝ) * 1 * 1 := by
              gcongr
              linarith
            have h2 : (t : ℝ) * 1 * 1 = (t : ℝ) := by ring
            rw [h2] at h1
            linarith
          have hr_pos : 0 < sg * (val (γ₁ s) + sg * ((t : ℝ) * (1 - t) * w s)) := by
            rw [mul_add, ← mul_assoc, hsgsq, one_mul]
            by_cases hsK' : s ∈ K
            · rw [hcK s hsK', mul_zero, zero_add]
              exact mul_pos (mul_pos htpos h1mt) hwpos'
            · have h2 := (hS1 s hsV hsK').2
              have h3 : 0 < (t : ℝ) * (1 - t) * w s := mul_pos (mul_pos htpos h1mt) hwpos'
              linarith
          have hr_abs : |val (γ₁ s) + sg * ((t : ℝ) * (1 - t) * w s)| < δ' := by
            have habs_sg : |sg * ((t : ℝ) * (1 - t) * w s)| = (t : ℝ) * (1 - t) * w s := by
              rcases hsgpm with h | h <;> rw [h]
              · rw [one_mul, abs_of_nonneg htw_nonneg]
              · rw [neg_one_mul, abs_neg, abs_of_nonneg htw_nonneg]
            have h1 : |val (γ₁ s)| < δ / 2 := by rw [hyval]; exact hy
            calc |val (γ₁ s) + sg * ((t : ℝ) * (1 - t) * w s)|
                ≤ |val (γ₁ s)| + |sg * ((t : ℝ) * (1 - t) * w s)| := abs_add_le _ _
              _ < δ / 2 + δ / 2 := by rw [habs_sg]; exact add_lt_add h1 htw_lt
              _ = δ := by ring
              _ ≤ δ' := hδleδ'
          have hg := glue_across hr_pos
          rw [show b - 1 + 1 = b by omega] at hg
          rw [← hg]
          refine hU'sub (hδ'sub ?_)
          exact ⟨_, Metric.mem_ball.mpr (by rw [Real.dist_eq, sub_zero]; exact hr_abs), rfl⟩
      exact Filter.mem_of_superset
        (prod_mem_nhds (hTopen.mem_nhds h0T) (hJopen.mem_nhds hsJ)) hmain
    · have hopen : IsOpen ({q : I × I | q.1 ≠ 0} ∪ {q : I × I | q.2 ∉ K}) := by
        refine IsOpen.union ?_ ?_
        · exact (_root_.isClosed_singleton (x := (0 : I))).isOpen_compl.preimage continuous_fst
        · exact hKclosed.isOpen_compl.preimage continuous_snd
      have hqO : q ∈ {q : I × I | q.1 ≠ 0} ∪ {q : I × I | q.2 ∉ K} := by
        rcases not_and_or.mp hq with h | h
        · exact .inl h
        · exact .inr h
      refine ContinuousAt.congr hQcont.continuousAt ?_
      refine Filter.eventuallyEq_of_mem (hopen.mem_nhds hqO) ?_
      intro q' hq'
      rcases hq' with h | h
      · change Q q' = (if q'.1 = 0 then γ₁ q'.2 else Q q')
        rw [if_neg h]
      · exact (hHQ _ h).symm
  -- endpoint facts and assembly
  have hQ1 : ∀ s, Q (1, s) ∈ chain a (b - 1) := by
    intro s
    by_cases hs : s ∈ V
    · rw [hQ_mem _ hs, show ((1 : I) : ℝ) = 1 from rfl, sub_self, mul_zero, zero_mul, mul_zero,
        add_zero]
      exact mk_mem_chain (by omega) le_rfl
    · rw [hQ_notmem _ hs]
      have hsK : s ∉ K := fun h ↦ hs (hKV h)
      exact (hγ₁ s).resolve_right fun h ↦ hsK ((hK_iff s).mpr h)
  refine ⟨⟨⟨fun s ↦ Q (1, s), hQcont.comp (continuous_const.prodMk continuous_id)⟩, ?_, ?_⟩,
    fun s ↦ hQ1 s, ?_⟩
  · exact (hQ_notmem (1, 0) h0V).trans γ₁.source
  · exact (hQ_notmem (1, 1) h1V).trans γ₁.target
  · refine ⟨⟨⟨⟨H, hHcont⟩, ?_, ?_⟩, ?_⟩⟩
    · intro s
      change (if (0 : I) = 0 then γ₁ s else Q (0, s)) = γ₁ s
      rw [if_pos rfl]
    · intro s
      change (if (1 : I) = 0 then γ₁ s else Q (1, s)) = Q (1, s)
      rw [if_neg hIone_ne]
    · intro t s hs
      rcases hs with rfl | hs
      · change (if t = 0 then γ₁ (0 : I) else Q (t, 0)) = γ₁ 0
        split_ifs
        · rfl
        · exact hQ_notmem (t, 0) h0V
      · rw [Set.mem_singleton_iff] at hs
        subst hs
        change (if t = 0 then γ₁ (1 : I) else Q (t, 1)) = γ₁ 1
        split_ifs
        · rfl
        · exact hQ_notmem (t, 1) h1V

/-! ### Reduction, combined and reflected -/

theorem reduce_top {a b : ℤ} (ha : a ≤ 0) (hb : 1 ≤ b) (γ : Path (mk 0 0) (mk 0 0))
    (hγ : ∀ s, γ s ∈ chain a b) :
    ∃ γ' : Path (mk 0 0) (mk 0 0), (∀ s, γ' s ∈ chain a (b - 1)) ∧ γ.Homotopic γ' := by
  obtain ⟨γ₁, h1, hh1⟩ := fold_top ha hb γ hγ
  obtain ⟨γ₂, h2, hh2⟩ := swap_top ha hb γ₁ h1
  exact ⟨γ₂, h2, hh1.trans hh2⟩

/-- Transport a loop at the base point through the reflection. -/
def transportLoop (γ : Path (mk 0 0) (mk 0 0)) : Path (mk 0 0) (mk 0 0) where
  toFun := fun s ↦ reflZ (γ s)
  continuous_toFun := continuous_reflZ.comp γ.continuous
  source' := by rw [γ.source, reflZ_base]
  target' := by rw [γ.target, reflZ_base]

lemma transportLoop_involutive (γ : Path (mk 0 0) (mk 0 0)) :
    transportLoop (transportLoop γ) = γ := by
  ext s
  exact reflZ_reflZ (γ s)

lemma transportLoop_homotopic {γ γ' : Path (mk 0 0) (mk 0 0)} (h : γ.Homotopic γ') :
    (transportLoop γ).Homotopic (transportLoop γ') := by
  obtain ⟨Hom⟩ := h
  refine ⟨⟨⟨⟨fun q ↦ reflZ (Hom q), continuous_reflZ.comp Hom.toContinuousMap.continuous⟩,
    ?_, ?_⟩, ?_⟩⟩
  · exact fun s ↦ congrArg reflZ (Hom.map_zero_left s)
  · exact fun s ↦ congrArg reflZ (Hom.map_one_left s)
  · exact fun t x hx ↦ congrArg reflZ (Hom.prop' t x hx)

theorem reduce_bot {a b : ℤ} (ha : a ≤ -1) (hb : 0 ≤ b) (γ : Path (mk 0 0) (mk 0 0))
    (hγ : ∀ s, γ s ∈ chain a b) :
    ∃ γ' : Path (mk 0 0) (mk 0 0), (∀ s, γ' s ∈ chain (a + 1) b) ∧ γ.Homotopic γ' := by
  have hγ' : ∀ s, transportLoop γ s ∈ chain (-b) (-a) := fun s ↦ reflZ_mem_chain (hγ s)
  obtain ⟨δ, hval, hhom⟩ := reduce_top (by omega) (by omega) (transportLoop γ) hγ'
  refine ⟨transportLoop δ, ?_, ?_⟩
  · intro s
    have h := reflZ_mem_chain (hval s)
    rw [show -(-a - 1) = a + 1 by omega, show -(-b) = b by omega] at h
    exact h
  · have h := transportLoop_homotopic hhom
    rw [transportLoop_involutive] at h
    exact h

/-! ### The base case: contracting a loop on a single sheet -/

open unitInterval in
lemma nullhomotopic_of_chain_zero (γ : Path (mk 0 0) (mk 0 0)) (hγ : ∀ s, γ s ∈ chain 0 0) :
    γ.Homotopic (Path.refl (mk 0 0)) := by
  have hform : ∀ s, γ s = mk (val (γ s)) 0 := by
    intro s
    obtain ⟨j, hj1, hj2, x, hx⟩ := mem_chain_iff.mp (hγ s)
    have hj : j = 0 := by omega
    subst hj
    rw [← hx]
    rfl
  refine ⟨⟨⟨⟨fun q ↦ mk ((1 - q.1) * val (γ q.2)) 0, ?_⟩, ?_, ?_⟩, ?_⟩⟩
  · refine (continuous_sheet 0).comp ?_
    exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      (continuous_val.comp (γ.continuous.comp continuous_snd))
  · intro s
    change mk ((1 - ((0 : I) : ℝ)) * val (γ s)) 0 = γ s
    rw [show ((0 : I) : ℝ) = 0 from rfl, sub_zero, one_mul]
    exact (hform s).symm
  · intro s
    change mk ((1 - ((1 : I) : ℝ)) * val (γ s)) 0 = _
    rw [show ((1 : I) : ℝ) = 1 from rfl, sub_self, zero_mul]
    rfl
  · intro t s hs
    rcases hs with rfl | hs
    · change mk ((1 - (t : ℝ)) * val (γ 0)) 0 = γ 0
      rw [γ.source, show val (mk 0 0) = 0 from rfl, mul_zero]
    · rw [Set.mem_singleton_iff] at hs
      subst hs
      change mk ((1 - (t : ℝ)) * val (γ 1)) 0 = γ 1
      rw [γ.target, show val (mk 0 0) = 0 from rfl, mul_zero]

/-! ### Every loop lies in a finite chain -/

lemma mem_chain_self (e : ZigZag) : ∃ N : ℕ, e ∈ chain (-(N : ℤ)) N := by
  obtain ⟨⟨x, n⟩⟩ := e
  exact ⟨n.natAbs, mem_chain_iff.mpr ⟨n, by omega, by omega, x, rfl⟩⟩

lemma exists_chain_bound (γ : Path (mk 0 0) (mk 0 0)) :
    ∃ N : ℕ, ∀ s, γ s ∈ chain (-(N : ℤ)) N := by
  have hcomp : IsCompact (Set.range γ) := isCompact_range γ.continuous
  have hsub : Set.range γ ⊆ ⋃ N : ℕ, chain (-(N : ℤ)) N := by
    rintro e ⟨s, rfl⟩
    obtain ⟨N, hN⟩ := mem_chain_self (γ s)
    exact Set.mem_iUnion.mpr ⟨N, hN⟩
  have hmono : Monotone fun N : ℕ ↦ chain (-(N : ℤ)) N := fun N M h ↦
    chain_mono (by omega) (by omega)
  obtain ⟨N, hN⟩ := hcomp.elim_directed_cover (fun N : ℕ ↦ chain (-(N : ℤ)) N)
    (fun N ↦ isOpen_chain _ _) hsub hmono.directed_le
  exact ⟨N, fun s ↦ hN ⟨s, rfl⟩⟩

/-! ### Every loop at the base point is null-homotopic -/

theorem loop_nullhomotopic (γ : Path (mk 0 0) (mk 0 0)) :
    γ.Homotopic (Path.refl (mk 0 0)) := by
  obtain ⟨N, hN⟩ := exists_chain_bound γ
  suffices h : ∀ (k : ℕ) (a b : ℤ), a ≤ 0 → 0 ≤ b → b - a ≤ k →
      ∀ γ : Path (mk 0 0) (mk 0 0), (∀ s, γ s ∈ chain a b) →
      γ.Homotopic (Path.refl (mk 0 0)) by
    exact h (N + N) (-(N : ℤ)) N (by omega) (by omega) (by omega) γ hN
  intro k
  induction k with
  | zero =>
    intro a b ha hb hab γ hγ
    obtain rfl : a = 0 := by omega
    obtain rfl : b = 0 := by omega
    exact nullhomotopic_of_chain_zero γ hγ
  | succ k ih =>
    intro a b ha hb hab γ hγ
    by_cases hb1 : 1 ≤ b
    · obtain ⟨γ', hval, hhom⟩ := reduce_top ha hb1 γ hγ
      exact hhom.trans (ih a (b - 1) ha (by omega) (by omega) γ' hval)
    · by_cases ha1 : a ≤ -1
      · obtain ⟨γ', hval, hhom⟩ := reduce_bot ha1 hb γ hγ
        exact hhom.trans (ih (a + 1) b (by omega) hb (by omega) γ' hval)
      · obtain rfl : a = 0 := by omega
        obtain rfl : b = 0 := by omega
        exact nullhomotopic_of_chain_zero γ hγ

/-! ### The zigzag is simply connected -/

open Path.Homotopic.Quotient in
instance : SimplyConnectedSpace ZigZag := by
  rw [simply_connected_iff_loops_nullhomotopic]
  refine ⟨inferInstance, fun x δ ↦ ?_⟩
  obtain ⟨α⟩ := joined_to_base x
  have hC := loop_nullhomotopic ((α.symm.trans δ).trans α)
  rw [← eq]
  have h0 : (⟦(α.symm.trans δ).trans α⟧ : Path.Homotopic.Quotient (mk 0 0) (mk 0 0)) =
      ⟦Path.refl (mk 0 0)⟧ := Quotient.sound hC
  have h1 := congrArg (fun P ↦ Path.Homotopic.Quotient.trans
    (Path.Homotopic.Quotient.trans ⟦α⟧ P) (Path.Homotopic.Quotient.symm ⟦α⟧)) h0
  have h2 : Path.Homotopic.Quotient.trans ⟦α⟧
      (Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.symm ⟦α⟧) ⟦δ⟧) =
      Path.Homotopic.Quotient.refl x := by
    simpa using h1
  have h3 := (Path.Homotopic.Quotient.trans_assoc ⟦α⟧
    (Path.Homotopic.Quotient.symm ⟦α⟧) ⟦δ⟧).trans h2
  have h4 := (congrArg (fun A ↦ Path.Homotopic.Quotient.trans A ⟦δ⟧)
    (Path.Homotopic.Quotient.trans_symm ⟦α⟧).symm).trans h3
  exact (Path.Homotopic.Quotient.refl_trans ⟦δ⟧).symm.trans h4

end ZigZag
