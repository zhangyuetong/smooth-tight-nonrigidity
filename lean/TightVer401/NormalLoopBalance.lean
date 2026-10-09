import TightVer401.NormalLoopArclength
import TightVer401.RuledPrimitives
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! The nonlinear balance density is derived from the actual physical
curvature and torsion. The change of variables is an actual integral identity. -/
namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

def normalLoopPhysicalK (a κ ψ : ℝ → ℝ) (s : ℝ) : ℝ := κ (ψ s) / a (ψ s)
def normalLoopPhysicalTau (a ψ : ℝ → ℝ) (s : ℝ) : ℝ := -(a (ψ s))⁻¹

theorem normalLoop_physical_rho {a ψ : ℝ → ℝ} {s : ℝ} (ha : 0 < a (ψ s)) :
    ruledRho (normalLoopPhysicalTau a ψ) s = (Real.sqrt (a (ψ s)))⁻¹ := by
  simp only [ruledRho, normalLoopPhysicalTau, abs_neg,
    abs_of_pos (inv_pos.mpr ha), Real.sqrt_inv]

theorem normalLoop_physical_D {a κ ψ : ℝ → ℝ} {s a' κ' : ℝ}
    (ha : HasDerivAt a a' (ψ s)) (hκ : HasDerivAt κ κ' (ψ s))
    (hpos : 0 < a (ψ s)) (hψ : HasDerivAt ψ (a (ψ s))⁻¹ s) :
    ruledD (normalLoopPhysicalK a κ ψ) (normalLoopPhysicalTau a ψ) s = κ' / (a (ψ s))^2 := by
  have hapsi := ha.comp s hψ
  have hκpsi := hκ.comp s hψ
  have hk : HasDerivAt (normalLoopPhysicalK a κ ψ)
      (((κ' * (a (ψ s))⁻¹) * a (ψ s) - κ (ψ s) * (a' * (a (ψ s))⁻¹)) /
        (a (ψ s))^2) s := hκpsi.div hapsi (ne_of_gt hpos)
  have ht : HasDerivAt (normalLoopPhysicalTau a ψ)
      (-(-(a' * (a (ψ s))⁻¹) / (a (ψ s))^2)) s :=
    (hapsi.inv (ne_of_gt hpos)).neg
  rw [ruledD, ruledLambda, hk.deriv, ht.deriv]
  dsimp [normalLoopPhysicalK, normalLoopPhysicalTau]
  field_simp
  <;> ring

theorem normalLoop_balance_density {a κ ψ : ℝ → ℝ} {s a' κ' : ℝ}
    (ha : HasDerivAt a a' (ψ s)) (hκ : HasDerivAt κ κ' (ψ s))
    (hpos : 0 < a (ψ s)) (hψ : HasDerivAt ψ (a (ψ s))⁻¹ s) :
    ruledPeriodCoefficient (normalLoopPhysicalK a κ ψ) (normalLoopPhysicalTau a ψ) s *
      a (ψ s) = κ' / (2 * Real.sqrt (a (ψ s))) := by
  rw [ruledPeriodCoefficient, normalLoop_physical_D ha hκ hpos hψ,
    normalLoop_physical_rho hpos]
  have hroot : Real.sqrt (a (ψ s)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
  field_simp
  <;> rw [Real.sq_sqrt hpos.le]

end
end TightVer401
