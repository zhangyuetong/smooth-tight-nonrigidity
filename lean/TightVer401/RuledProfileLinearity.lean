import TightVer401.RuledProfileSupport

/-! Linearity is proved for the actual vector fields and actual profile
derivatives. This does not replace the global kernel classification. -/
namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry

theorem ruledProfileField_add {k τ ρ W F G : ℝ → ℝ} {T n : ℝ → Ambient}
    (hF : Differentiable ℝ F) (hG : Differentiable ℝ G) :
    ruledProfileField k τ ρ W (F + G) T n =
      ruledProfileField k τ ρ W F T n + ruledProfileField k τ ρ W G T n := by
  funext p
  simp only [ruledProfileField, ruledBending, ruledProfileAlpha, ruledProfileBeta,
    deriv_add (hF (ruledFirstIntegral ρ W p)) (hG (ruledFirstIntegral ρ W p)), Pi.add_apply]
  module

theorem ruledProfileField_smul (k τ ρ W F : ℝ → ℝ) (T n : ℝ → Ambient) (a : ℝ) :
    ruledProfileField k τ ρ W (fun v => a * F v) T n =
      a • ruledProfileField k τ ρ W F T n := by
  funext p
  simp only [ruledProfileField, ruledBending, ruledProfileAlpha, ruledProfileBeta,
    deriv_const_mul_field, Pi.smul_apply, smul_eq_mul]
  module

end
end TightVer401
