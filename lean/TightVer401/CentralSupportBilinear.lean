import TightVer401.SphereSupportTensor
import TightVer401.RuledNormal

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

def sphereSupportTensorBilinear (g : MetricField) (H : Coord → ℝ)
    (p v w : Coord) : ℝ := v ⬝ᵥ (sphereSupportTensor g H p *ᵥ w)

theorem sphereSupportTensorBilinear_eq_differential
    {g : MetricField} {Q : Coord → Ambient} {H : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hQ : IsometricOn g Q U)
    (hH : ContDiffOn ℝ ∞ H U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U)
    (hunit : ∀ q ∈ U, inner ℝ (Q q) (Q q) = 1) (v w : Coord) :
    sphereSupportTensorBilinear g H p v w =
      inner ℝ (fderiv ℝ (sphereSupportMap g Q H) p v) (fderiv ℝ Q p w) := by
  rw [fderiv_two_coordinates, fderiv_two_coordinates, inner_add_left,
    inner_add_right, inner_add_right]
  simp only [real_inner_smul_left, real_inner_smul_right]
  rw [(sphereSupportMap_differential_pairings hg hQ hH hU hp hunit 0 0).2,
    (sphereSupportMap_differential_pairings hg hQ hH hU hp hunit 0 1).2,
    (sphereSupportMap_differential_pairings hg hQ hH hU hp hunit 1 0).2,
    (sphereSupportMap_differential_pairings hg hQ hH hU hp hunit 1 1).2]
  simp only [sphereSupportTensorBilinear, sphereSupportTensor, dotProduct,
    Matrix.mulVec, Fin.sum_univ_two, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

end
end TightVer401
