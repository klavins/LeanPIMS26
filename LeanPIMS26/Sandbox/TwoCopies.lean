import Mathlib

open Topology

def TwoR := ℝ ⊕ ℝ

instance : TopologicalSpace TwoR := inferInstanceAs (TopologicalSpace (ℝ ⊕ ℝ))

namespace TwoR

def val : TwoR → ℝ
  | .inl a => a
  | .inr a => a

def rel (x y : TwoR) : Prop := x = y ∨ (x.val = y.val ∧ x.val ≠ 0)

def setoid : Setoid TwoR where
  r := rel
  iseqv := by
    refine ⟨fun x ↦ .inl rfl, ?_, ?_⟩
    · rintro x y (rfl | ⟨h, h0⟩)
      · exact .inl rfl
      · exact .inr ⟨h.symm, h ▸ h0⟩
    · rintro x y z (rfl | ⟨h1, h0⟩) (rfl | ⟨h2, h0'⟩)
      · exact .inl rfl
      · exact .inr ⟨h2, h0'⟩
      · exact .inr ⟨h1, h0⟩
      · exact .inr ⟨h1.trans h2, h0⟩

end TwoR

def TwoOrigins := Quotient TwoR.setoid

instance : TopologicalSpace TwoOrigins := inferInstanceAs (TopologicalSpace (Quotient _))

namespace TwoOrigins

def q : TwoR → TwoOrigins := Quotient.mk TwoR.setoid

theorem continuous_q : Continuous q := continuous_quotient_mk'

def o₁ : TwoOrigins := q (.inl 0)
def o₂ : TwoOrigins := q (.inr 0)

theorem o₁_ne_o₂ : o₁ ≠ o₂ :=
  fun h ↦ Or.elim (Quotient.exact h) (fun h ↦ Sum.inl_ne_inr h) (fun h ↦ h.2 rfl)

theorem glue {t : ℝ} (ht : t ≠ 0) : q (.inl t) = q (.inr t) := Quotient.sound (.inr ⟨rfl, ht⟩)

private lemma exists_ne_zero_mem {A B : Set ℝ} (hA : A ∈ 𝓝 (0 : ℝ)) (hB : B ∈ 𝓝 (0 : ℝ)) :
    ∃ t : ℝ, t ≠ 0 ∧ t ∈ A ∧ t ∈ B := by
  have h : A ∩ B ∈ 𝓝[≠] (0 : ℝ) := mem_nhdsWithin_of_mem_nhds (Filter.inter_mem hA hB)
  obtain ⟨t, ⟨htA, htB⟩, ht⟩ := Filter.nonempty_of_mem (Filter.inter_mem h self_mem_nhdsWithin)
  exact ⟨t, ht, htA, htB⟩

theorem nhds_overlap {U V : Set TwoOrigins} (hU : IsOpen U) (hV : IsOpen V)
    (h₁ : o₁ ∈ U) (h₂ : o₂ ∈ V) : (U ∩ V).Nonempty := by
  obtain ⟨t, ht, htU, htV⟩ := exists_ne_zero_mem
    ((hU.preimage (continuous_q.comp continuous_inl)).mem_nhds h₁)
    ((hV.preimage (continuous_q.comp continuous_inr)).mem_nhds h₂)
  exact ⟨q (.inl t), htU, glue ht ▸ htV⟩

theorem not_t2 : ¬ T2Space TwoOrigins := by
  intro h
  obtain ⟨U, V, hU, hV, h₁, h₂, hUV⟩ := t2_separation o₁_ne_o₂
  obtain ⟨w, hwU, hwV⟩ := nhds_overlap hU hV h₁ h₂
  exact Set.disjoint_left.mp hUV hwU hwV

end TwoOrigins
