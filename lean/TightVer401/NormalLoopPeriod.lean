import TightVer401.NormalLoopGlobalArclength
import TightVer401.PeriodicRuledFrame

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

theorem normalLoop_whole_period_balance {a κ : ℝ → ℝ} {L : ℝ}
    (ha : ContDiff ℝ ∞ a) (hκ : ContDiff ℝ ∞ κ) (hpos : ∀ r, 0 < a r)
    (hperiod : Function.Periodic a L) (hL : 0 < L) :
    ∃ e : ℝ ≃ₜ ℝ, (e : ℝ → ℝ) = rawPrimitive a ∧ ContDiff ℝ ∞ e.symm ∧
      (∀ s, HasDerivAt e.symm (a (e.symm s))⁻¹ s) ∧
      (∀ s, e.symm (s + rawPrimitive a L) = e.symm s + L) ∧
      (∫ s in 0..rawPrimitive a L,
        ruledPeriodCoefficient (normalLoopPhysicalK a κ e.symm)
          (normalLoopPhysicalTau a e.symm) s) =
        (1 / 2 : ℝ) * (∫ r in 0..L, deriv κ r / Real.sqrt (a r)) := by
  obtain ⟨e, hefun, hsmooth, hderiv, hshift⟩ :=
    normalLoop_exists_global_arclength_inverse ha hpos hperiod hL
  refine ⟨e, hefun, hsmooth, hderiv, hshift, ?_⟩
  have hi := normalLoop_balance_integral_on_chart (r₀ := 0) (r₁ := L)
    ha hκ hpos e.toOpenPartialHomeomorph hefun (by simp)
  have hinv : (e.toOpenPartialHomeomorph.symm : ℝ → ℝ) = e.symm := rfl
  rw [hinv] at hi
  simpa only [rawPrimitive, intervalIntegral.integral_same] using hi

end
end TightVer401
