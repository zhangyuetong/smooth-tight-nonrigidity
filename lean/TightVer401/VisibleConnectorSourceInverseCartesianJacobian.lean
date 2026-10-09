import TightVer401.VisibleConnectorSourceInverseJacobian
import TightVer401.VisibleConnectorCartesianDescent
import TightVer401.QuadraticRadialFillingCircle

/-! Actual Jacobian of the literal descended connector source, including both
boundaries of the closed round annulus. -/
namespace TightVer401
noncomputable section
open Set Function Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix

theorem visibleConnectorSourceInverse_cartesian_smooth
    {L : ℝ} {p w : ℝ → Coord} {h : ℝ → ℝ}
    (hp : ContDiff ℝ ∞ p) (hw : ContDiff ℝ ∞ w) (hh : ContDiff ℝ ∞ h)
    (hpL : Periodic p L) (hwL : Periodic w L) (hhL : Periodic h L) :
    ContDiffOn ℝ ∞ (visibleConnectorCartesianSource L p w h)
      {z | 0 < planarRadius z} := by
  apply contDiffOn_pi.mpr
  intro i
  exact angularDescentPotential_contDiffOn
    ((contDiff_apply ℝ ℝ i).comp (visibleConnectorPolarSource_contDiff hp hw hh))
    (fun r theta => congrFun (visibleConnectorPolarSource_periodic hpL hwL hhL r theta) i)

theorem visibleConnectorSourceInverse_cartesian_jacobian_polar
    {L : ℝ} {p w : ℝ → Coord} {h : ℝ → ℝ}
    (hp : ContDiff ℝ ∞ p) (hw : ContDiff ℝ ∞ w) (hh : ContDiff ℝ ∞ h)
    (hpL : Periodic p L) (hwL : Periodic w L) (hhL : Periodic h L)
    (gamma : ℝ → Coord) (q : Coord) (hq : 0 < q 0) :
    annularJacobian (visibleConnectorCartesianSource L p w h) (saddlePolarChart q) =
      (L / (2 * Real.pi)) * h (L * q 1 / (2 * Real.pi)) *
        visibleConnectorDelta p gamma w (visibleConnectorSourceInverseClock L h q) / q 0 := by
  have hOpen : IsOpen {z : Coord | 0 < planarRadius z} :=
    isOpen_lt continuous_const quadraticRadialFillingRadius_continuous
  have hz : saddlePolarChart q ∈ {z : Coord | 0 < planarRadius z} := by
    change 0 < planarRadius (saddlePolarChart q)
    rw [angularDescent_radius_polar hq]
    exact hq
  have hF := (visibleConnectorSourceInverse_cartesian_smooth hp hw hh hpL hwL hhL).contDiffAt
    (hOpen.mem_nhds hz)
  apply visibleConnectorSourceInverseJacobian_of_polar_germ L hp hw hh gamma q hq
    (hF.differentiableAt (by simp))
  change (visibleConnectorCartesianSource L p w h ∘ saddlePolarChart) =ᶠ[nhds q]
    visibleConnectorPolarSource L p w h
  exact visibleConnectorCartesianSource_polar_germ hpL hwL hhL hq

theorem visibleConnectorSourceInverse_polar_representative (z : Coord) :
    saddlePolarChart ![planarRadius z, Complex.arg (angularDescentComplex z)] = z := by
  ext i
  fin_cases i
  · change planarRadius z * Real.cos (Complex.arg (angularDescentComplex z)) = z 0
    rw [← angularDescentComplex_norm]
    rw [Complex.norm_mul_cos_arg]
    simp [angularDescentComplex]
  · change planarRadius z * Real.sin (Complex.arg (angularDescentComplex z)) = z 1
    rw [← angularDescentComplex_norm]
    rw [Complex.norm_mul_sin_arg]
    simp [angularDescentComplex]

theorem visibleConnectorSourceInverse_cartesian_positive_closed
    {L : ℝ} (hL : 0 < L) {p w : ℝ → Coord} {h : ℝ → ℝ}
    (hp : ContDiff ℝ ∞ p) (hw : ContDiff ℝ ∞ w) (hh : ContDiff ℝ ∞ h)
    (hpL : Periodic p L) (hwL : Periodic w L) (hhL : Periodic h L)
    (hpos : ∀ s, 0 < h s) (gamma : ℝ → Coord)
    (hDelta : ∀ q : Coord, 0 ≤ q 1 → q 1 ≤ h (q 0) →
      0 < visibleConnectorDelta p gamma w q) :
    ∀ z : Coord, 1 ≤ planarRadius z → planarRadius z ≤ 2 →
      0 < annularJacobian (visibleConnectorCartesianSource L p w h) z := by
  intro z hz1 hz2
  let q : Coord := ![planarRadius z, Complex.arg (angularDescentComplex z)]
  have hr : 0 < q 0 := by dsimp [q]; linarith
  have heq : saddlePolarChart q = z := visibleConnectorSourceInverse_polar_representative z
  rw [← heq, visibleConnectorSourceInverse_cartesian_jacobian_polar hp hw hh hpL hwL hhL gamma q hr]
  have hhq := hpos (L * q 1 / (2 * Real.pi))
  have hu0 : 0 ≤ (visibleConnectorSourceInverseClock L h q) 1 := by
    change 0 ≤ (planarRadius z - 1) * h (L * q 1 / (2 * Real.pi))
    exact mul_nonneg (sub_nonneg.mpr hz1) hhq.le
  have hu1 : (visibleConnectorSourceInverseClock L h q) 1 ≤
      h ((visibleConnectorSourceInverseClock L h q) 0) := by
    change (planarRadius z - 1) * h (L * q 1 / (2 * Real.pi)) ≤
      h (L * q 1 / (2 * Real.pi))
    nlinarith
  exact div_pos (mul_pos (mul_pos (div_pos hL Real.two_pi_pos) hhq)
    (hDelta _ hu0 hu1)) hr

end
end TightVer401
