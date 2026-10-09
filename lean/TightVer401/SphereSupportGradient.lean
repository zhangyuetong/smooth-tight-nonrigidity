import TightVer401.SphereGeometry

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

def sphereGradient (g : MetricField) (Q : Coord → Ambient) (H : Coord → ℝ) : Coord → Ambient :=
  fun p => ∑ i, ((g p)⁻¹ *ᵥ (fun j => coordPartial j H p)) i • coordPartial i Q p

def sphereSupportMap (g : MetricField) (Q : Coord → Ambient) (H : Coord → ℝ) : Coord → Ambient :=
  fun p => sphereGradient g Q H p + H p • Q p

theorem sphereGradient_contDiffOn {g : MetricField} {Q : Coord → Ambient} {H : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hQ : ContDiffOn ℝ ∞ Q U)
    (hH : ContDiffOn ℝ ∞ H U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (sphereGradient g Q H) U := by
  apply ContDiffOn.sum
  intro i _
  have hcoef : ContDiffOn ℝ ∞
      (fun p => ((g p)⁻¹ *ᵥ (fun j => coordPartial j H p)) i) U := by
    change ContDiffOn ℝ ∞ (fun p => ∑ j, inverseMetric g p i j * coordPartial j H p) U
    apply ContDiffOn.sum
    intro j _
    exact (inverseMetric_contDiffOn hg i j).mul (partial_contDiffOn hH hU j)
  exact hcoef.smul (partial_contDiffOn hQ hU i)

theorem sphereSupportMap_contDiffOn {g : MetricField} {Q : Coord → Ambient} {H : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hQ : ContDiffOn ℝ ∞ Q U)
    (hH : ContDiffOn ℝ ∞ H U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (sphereSupportMap g Q H) U :=
  (sphereGradient_contDiffOn hg hQ hH hU).add (hH.smul hQ)

theorem sphereGradient_pairing {g : MetricField} {Q : Coord → Ambient} {H : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hQ : IsometricOn g Q U)
    {p : Coord} (hp : p ∈ U) (j : Fin 2) :
    inner ℝ (sphereGradient g Q H p) (coordPartial j Q p) = coordPartial j H p := by
  have hind (i j : Fin 2) : inner ℝ (coordPartial i Q p) (coordPartial j Q p) = g p i j :=
    congrFun (congrFun (inducedMetric_eq_of_isometric hQ hp) i) j
  have he : g p *ᵥ ((g p)⁻¹ *ᵥ (fun k => coordPartial k H p)) = (fun k => coordPartial k H p) := by
    rw [Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (hg.2 p hp).isUnit),
      Matrix.one_mulVec]
  have hj := congrFun he j
  simp only [sphereGradient, sum_inner, real_inner_smul_left, hind,
    metric_coeff_symm hg hp] 
  simpa only [Matrix.mulVec, dotProduct, mul_comm] using hj

theorem sphereGradient_normal_pairing {g : MetricField} {Q : Coord → Ambient} {H : Coord → ℝ}
    {U : Set Coord} (hQ : ContDiffOn ℝ ∞ Q U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U)
    (hunit : ∀ q ∈ U, inner ℝ (Q q) (Q q) = 1) :
    inner ℝ (sphereGradient g Q H p) (Q p) = 0 := by
  have horth (i : Fin 2) : inner ℝ (coordPartial i Q p) (Q p) = 0 :=
    sphere_differential_orthogonal hQ hU hp hunit _
  simp only [sphereGradient, sum_inner, real_inner_smul_left, horth, mul_zero, Finset.sum_const_zero]

theorem sphereSupportMap_height {g : MetricField} {Q : Coord → Ambient} {H : Coord → ℝ}
    {U : Set Coord} (hQ : ContDiffOn ℝ ∞ Q U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U)
    (hunit : ∀ q ∈ U, inner ℝ (Q q) (Q q) = 1) :
    inner ℝ (sphereSupportMap g Q H p) (Q p) = H p := by
  simp only [sphereSupportMap, inner_add_left, sphereGradient_normal_pairing hQ hU hp hunit,
    real_inner_smul_left, hunit p hp, mul_one, zero_add]

end
end TightVer401
