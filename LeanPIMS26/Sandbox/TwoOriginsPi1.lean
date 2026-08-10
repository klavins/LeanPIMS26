import LeanPIMS26.Sandbox.TwoOriginsSimplyConnected

namespace ZigZag

/-- The canonical point of the fiber of the covering map over the first origin. -/
def e₀ : p ⁻¹' {TwoOrigins.o₁} :=
  ⟨mk 0 0, by
    change p (mk 0 0) = TwoOrigins.o₁
    rw [p_mk, proj_even ⟨0, by ring⟩]
    rfl⟩

/-- The fundamental group of the line with two origins is the integers under addition
(written multiplicatively as `Multiplicative ℤ`). -/
noncomputable def pi1TwoOrigins :
    FundamentalGroup TwoOrigins TwoOrigins.o₁ ≃* Multiplicative ℤ :=
  (isAddQuotientCoveringMap_p.fundamentalGroupEquiv e₀).trans
    (MulOpposite.opMulEquiv (M := Multiplicative ℤ)).symm

theorem pi1TwoOrigins_nonempty :
    Nonempty (FundamentalGroup TwoOrigins TwoOrigins.o₁ ≃* Multiplicative ℤ) :=
  ⟨pi1TwoOrigins⟩

end ZigZag
