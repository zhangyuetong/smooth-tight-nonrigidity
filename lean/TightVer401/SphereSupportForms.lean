import TightVer401.SphereSupportTensor

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

theorem sphereSupportTensor_symm {g : MetricField} {H : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hH : ContDiffOn ℝ ∞ H U) (hU : IsOpen U)
    {p : Coord} (hp : p ∈ U) (i j : Fin 2) :
    sphereSupportTensor g H p i j = sphereSupportTensor g H p j i := by
  change covHessian g H p i j + H p * g p i j = covHessian g H p j i + H p * g p j i
  rw [covHessian_symm hg hU hH hp i j, metric_coeff_symm hg hp i j]

theorem sphereSupportMap_isUnitNormal {g : MetricField} {Q : Coord → Ambient} {H : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hQ : IsometricOn g Q U)
    (hH : ContDiffOn ℝ ∞ H U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U)
    (hunit : ∀ q ∈ U, inner ℝ (Q q) (Q q) = 1) :
    IsUnitNormalAt (sphereSupportMap g Q H) (Q p) p := by
  refine ⟨hunit p hp, fun v => ?_⟩
  rw [fderiv_two_coordinates]
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left,
    (sphereSupportMap_differential_pairings hg hQ hH hU hp hunit 0 0).1,
    (sphereSupportMap_differential_pairings hg hQ hH hU hp hunit 1 1).1]
  simp

theorem sphereSupportMap_secondFundamental {g : MetricField} {Q : Coord → Ambient} {H : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hQ : IsometricOn g Q U)
    (hH : ContDiffOn ℝ ∞ H U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U)
    (hunit : ∀ q ∈ U, inner ℝ (Q q) (Q q) = 1) :
    secondFundamental (sphereSupportMap g Q H) (Q p) p = -sphereSupportTensor g H p := by
  ext i j
  have hA := sphereSupportMap_contDiffOn hg hQ.1 hH hU
  have hdj := (((partial_contDiffOn hA hU j) p hp).contDiffAt
    (hU.mem_nhds hp)).differentiableAt (by simp)
  have hdQ := ((hQ.1 p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have he : (fun q => inner ℝ (coordPartial j (sphereSupportMap g Q H) q) (Q q)) =ᶠ[𝓝 p]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact (sphereSupportMap_differential_pairings hg hQ hH hU hq hunit j j).1
  have hi := coordPartial_eventuallyEq he i
  rw [coordPartial_inner hdj hdQ] at hi
  have hz : coordPartial i (fun _ : Coord => (0 : ℝ)) p = 0 := by
    unfold coordPartial
    rw [(hasFDerivAt_const (c := (0 : ℝ)) p).fderiv]
    rfl
  rw [hz, (sphereSupportMap_differential_pairings hg hQ hH hU hp hunit j i).2] at hi
  change sphereSupportTensor g H p j i + secondFundamental (sphereSupportMap g Q H) (Q p) p i j = 0 at hi
  change secondFundamental (sphereSupportMap g Q H) (Q p) p i j = -sphereSupportTensor g H p i j
  rw [sphereSupportTensor_symm hg hH hU hp j i] at hi
  linarith

theorem sphereTangentLift_inner {g : MetricField} {Q : Coord → Ambient} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hQ : IsometricOn g Q U) {p : Coord} (hp : p ∈ U)
    (a b : Coord) : inner ℝ (sphereTangentLift g Q p a) (sphereTangentLift g Q p b) =
      a ⬝ᵥ ((g p)⁻¹ *ᵥ b) := by
  change inner ℝ (sphereTangentLift g Q p a)
    (∑ i, ((g p)⁻¹ *ᵥ b) i • coordPartial i Q p) = _
  simp only [inner_sum, real_inner_smul_right, sphereTangentLift_pairing hg hQ hp,
    dotProduct, mul_comm]

theorem sphereSupportMap_inducedMetric {g : MetricField} {Q : Coord → Ambient} {H : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hQ : IsometricOn g Q U)
    (hH : ContDiffOn ℝ ∞ H U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U)
    (hunit : ∀ q ∈ U, inner ℝ (Q q) (Q q) = 1) :
    inducedMetric (sphereSupportMap g Q H) p =
      sphereSupportTensor g H p * (g p)⁻¹ * (sphereSupportTensor g H p).transpose := by
  ext i j
  rw [inducedMetric, sphereSupportMap_differential hg hQ hH hU hp hunit i,
    sphereSupportMap_differential hg hQ hH hU hp hunit j, sphereTangentLift_inner hg hQ hp]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]
  ring

end
end TightVer401
