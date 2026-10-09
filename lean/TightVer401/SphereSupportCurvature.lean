import TightVer401.SphereSupportForms

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

def sphereSupportEndomorphism (g : MetricField) (H : Coord → ℝ) : MetricField :=
  fun p => (g p)⁻¹ * sphereSupportTensor g H p

theorem sphereSupportMap_differential_injective {g : MetricField} {Q : Coord → Ambient} {H : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hQ : IsometricOn g Q U)
    (hH : ContDiffOn ℝ ∞ H U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U)
    (hunit : ∀ q ∈ U, inner ℝ (Q q) (Q q) = 1)
    (hdet : (sphereSupportTensor g H p).det ≠ 0) :
    Function.Injective (fderiv ℝ (sphereSupportMap g Q H) p) := by
  intro v w hvw
  have hz : fderiv ℝ (sphereSupportMap g Q H) p (v - w) = 0 := by simp [map_sub, hvw]
  have hzero : sphereSupportTensor g H p *ᵥ (v - w) = 0 := by
    ext j
    have hj := congrArg (fun a => inner ℝ a (coordPartial j Q p)) hz
    rw [fderiv_two_coordinates, inner_add_left, real_inner_smul_left, real_inner_smul_left] at hj
    rw [(sphereSupportMap_differential_pairings hg hQ hH hU hp hunit 0 j).2,
      (sphereSupportMap_differential_pairings hg hQ hH hU hp hunit 1 j).2, inner_zero_left] at hj
    change (v - w) 0 * sphereSupportTensor g H p 0 j +
      (v - w) 1 * sphereSupportTensor g H p 1 j = 0 at hj
    rw [sphereSupportTensor_symm hg hH hU hp 0 j, sphereSupportTensor_symm hg hH hU hp 1 j] at hj
    simpa only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.zero_apply, mul_comm] using hj
  have heq : (sphereSupportTensor g H p)⁻¹ *ᵥ (sphereSupportTensor g H p *ᵥ (v - w)) = v - w := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]
  rw [hzero, Matrix.mulVec_zero] at heq
  exact sub_eq_zero.mp heq.symm

theorem sphereSupportMap_curvature {g : MetricField} {Q : Coord → Ambient} {H : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hQ : IsometricOn g Q U)
    (hH : ContDiffOn ℝ ∞ H U) (hU : IsOpen U)
    (hunit : ∀ q ∈ U, inner ℝ (Q q) (Q q) = 1)
    (hdet : ∀ q ∈ U, (sphereSupportTensor g H q).det ≠ 0)
    {p : Coord} (hp : p ∈ U) :
    gaussianCurvature (inducedMetric (sphereSupportMap g Q H)) p =
      1 / (sphereSupportEndomorphism g H p).det := by
  have hA := sphereSupportMap_contDiffOn hg hQ.1 hH hU
  have hgA := inducedMetric_smoothPositiveOn hA hU
    (fun q hq => sphereSupportMap_differential_injective hg hQ hH hU hq hunit (hdet q hq))
  rw [curvature_eq_second_form_det_div_metric_det hgA (inducedMetric_isometricOn hA) hU hp
    (sphereSupportMap_isUnitNormal hg hQ hH hU hp hunit),
    sphereSupportMap_secondFundamental hg hQ hH hU hp hunit,
    sphereSupportMap_inducedMetric hg hQ hH hU hp hunit]
  have hneg : (-sphereSupportTensor g H p).det = (sphereSupportTensor g H p).det := by
    simp only [Matrix.det_fin_two, Matrix.neg_apply]
    ring
  rw [hneg]
  simp only [sphereSupportEndomorphism, Matrix.det_mul, Matrix.det_transpose,
    Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  field_simp [metricDet_ne_zero hg hp, hdet p hp]

end
end TightVer401
