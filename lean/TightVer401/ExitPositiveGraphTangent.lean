import TightVer401.ExitPositiveGraphQuadratic

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff Matrix
set_option backward.isDefEq.respectTransparency false

def exitGraphCurve (v : ℝ → ℝ) (δ r : ℝ) : Coord := ![r, δ * v r]

theorem exitGraphCurve_contDiff {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v) (δ : ℝ) :
    ContDiff ℝ ∞ (exitGraphCurve v δ) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_id
  · exact contDiff_const.mul hv

theorem exitGraphCurve_hasDerivAt {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v) (δ r : ℝ) :
    HasDerivAt (exitGraphCurve v δ) (![1, δ * deriv v r] : Coord) r := by
  have h0 := (hasDerivAt_id r).smul_const (Pi.single 0 1 : Coord)
  have h1 := ((hv.differentiable (by simp) r).hasDerivAt.const_mul δ).smul_const
    (Pi.single 1 1 : Coord)
  convert! h0.add h1 using 1
  · funext s
    ext i
    fin_cases i <;> simp [exitGraphCurve]
  · ext i
    fin_cases i <;> simp

theorem exitGraphCurve_deriv {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v) (δ r : ℝ) :
    deriv (exitGraphCurve v δ) r = (![1, δ * deriv v r] : Coord) :=
  (exitGraphCurve_hasDerivAt hv δ r).deriv

theorem exitGraphQuadratic_actual_tangent {ℓ M N : Coord → ℝ} {v : ℝ → ℝ}
    (hv : ContDiff ℝ ∞ v) (δ r : ℝ) :
    exitGraphQuadratic ℓ M N v ![r, δ] =
      dotProduct (deriv (exitGraphCurve v δ) r)
        (!![ℓ (exitGraphCurve v δ r), M (exitGraphCurve v δ r);
          M (exitGraphCurve v δ r), N (exitGraphCurve v δ r)] *ᵥ
          deriv (exitGraphCurve v δ) r) := by
  rw [exitGraphCurve_deriv hv δ r]
  exact exitGraphQuadratic_matrix ℓ M N v r δ

end
end TightVer401
