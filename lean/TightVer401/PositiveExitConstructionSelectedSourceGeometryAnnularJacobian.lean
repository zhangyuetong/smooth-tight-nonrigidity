import TightVer401.PositiveExitConstructionSelectedSourceGeometryAnnularDescent
import TightVer401.VisibleConnectorSourceInverseJacobian

/-! Actual Jacobian of the SAME periodic angular descent. The full Cartesian
map and its polar representative share one literal germ; radius division is
computed from the checked polar-chart determinant. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

theorem positiveExitSelectedAnnularDescent_jacobian
    {W : Coord → Coord} {R : Set ℝ} (hR : IsOpen R)
    (hW : ContDiffOn ℝ ∞ W {q : Coord | q 0 ∈ R})
    (hperiod : ∀ r theta : ℝ, W ![r, theta + 2 * Real.pi] = W ![r, theta])
    {q : Coord} (hq : 0 < q 0) (hqR : q 0 ∈ R) :
    annularJacobian (positiveExitSelectedAnnularDescent W) (saddlePolarChart q) =
      annularJacobian W q / q 0 := by
  have hO := positiveExitSelectedAnnularDescentDomain_isOpen hR
  have hpO : saddlePolarChart q ∈ positiveExitSelectedAnnularDescentDomain R := by
    change 0 < planarRadius (saddlePolarChart q) ∧ planarRadius (saddlePolarChart q) ∈ R
    rw [angularDescent_radius_polar hq]
    exact ⟨hq, hqR⟩
  have hF := ((positiveExitSelectedAnnularDescent_contDiffOn hR hW hperiod)
    (saddlePolarChart q) hpO).contDiffAt (hO.mem_nhds hpO)
  have hGerm : (positiveExitSelectedAnnularDescent W ∘ saddlePolarChart) =ᶠ[𝓝 q] W := by
    filter_upwards [(isOpen_lt continuous_const (continuous_apply 0)).mem_nhds hq] with p hp
    exact positiveExitSelectedAnnularDescent_polar hperiod hp
  apply (eq_div_iff hq.ne').mpr
  rw [← visibleConnectorSourceInverseJacobian_polar_chart q,
    ← visibleConnectorSourceInverseJacobian_comp (hF.differentiableAt (by simp))
      (saddlePolarChart_contDiff.differentiable (by simp) q)]
  unfold annularJacobian
  rw [hGerm.fderiv_eq (𝕜 := ℝ)]

/-- Positive polar-coordinate source orientation gives the actual positive
Cartesian orientation of that SAME descended map at every positive radius. -/
theorem positiveExitSelectedAnnularDescent_jacobian_pos
    {W : Coord → Coord} {R : Set ℝ} (hR : IsOpen R)
    (hW : ContDiffOn ℝ ∞ W {q : Coord | q 0 ∈ R})
    (hperiod : ∀ r theta : ℝ, W ![r, theta + 2 * Real.pi] = W ![r, theta])
    {q : Coord} (hq : 0 < q 0) (hqR : q 0 ∈ R)
    (hJ : 0 < annularJacobian W q) :
    0 < annularJacobian (positiveExitSelectedAnnularDescent W) (saddlePolarChart q) := by
  rw [positiveExitSelectedAnnularDescent_jacobian hR hW hperiod hq hqR]
  exact div_pos hJ hq

end
end TightVer401
