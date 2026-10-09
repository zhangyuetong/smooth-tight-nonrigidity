import TightVer401.SphereSupportDifferential

/-! Regularity of the Gauss map is a consequence of nonzero curvature and the
actual differentiated normal equations. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

theorem gaussMap_partial_pairing {X N : Coord → Ambient} {U : Set Coord}
    (hX : ContDiffOn ℝ ∞ X U) (hN : ContDiffOn ℝ ∞ N U) (hU : IsOpen U)
    (hn : ∀ q ∈ U, IsUnitNormalAt X (N q) q) {p : Coord} (hp : p ∈ U) (i j : Fin 2) :
    inner ℝ (coordPartial i N p) (coordPartial j X p) = -secondFundamental X (N p) p i j := by
  have hdj := (((partial_contDiffOn hX hU j) p hp).contDiffAt
    (hU.mem_nhds hp)).differentiableAt (by simp)
  have hdN := ((hN p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have he : (fun q => inner ℝ (coordPartial j X q) (N q)) =ᶠ[𝓝 p] (fun _ => (0 : ℝ)) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact (hn q hq).2 _
  have hi := coordPartial_eventuallyEq he i
  rw [coordPartial_inner hdj hdN] at hi
  have hz : coordPartial i (fun _ : Coord => (0 : ℝ)) p = 0 := by
    unfold coordPartial
    rw [(hasFDerivAt_const (c := (0 : ℝ)) p).fderiv]
    rfl
  rw [hz] at hi
  change inner ℝ (coordPartial j X p) (coordPartial i N p) + secondFundamental X (N p) p i j = 0 at hi
  rw [real_inner_comm]
  linarith

theorem gaussMap_differential_injective_of_second_form {X N : Coord → Ambient} {U : Set Coord}
    (hX : ContDiffOn ℝ ∞ X U) (hN : ContDiffOn ℝ ∞ N U) (hU : IsOpen U)
    (hn : ∀ q ∈ U, IsUnitNormalAt X (N q) q) {p : Coord} (hp : p ∈ U)
    (hdet : (secondFundamental X (N p) p).det ≠ 0) : Function.Injective (fderiv ℝ N p) := by
  intro v z hvz
  have hz : fderiv ℝ N p (v - z) = 0 := by simp [map_sub, hvz]
  have hzero : (secondFundamental X (N p) p).transpose *ᵥ (v - z) = 0 := by
    ext j
    have hj := congrArg (fun a => inner ℝ a (coordPartial j X p)) hz
    rw [fderiv_two_coordinates, inner_add_left, real_inner_smul_left, real_inner_smul_left] at hj
    rw [gaussMap_partial_pairing hX hN hU hn hp 0 j,
      gaussMap_partial_pairing hX hN hU hn hp 1 j, inner_zero_left] at hj
    have hj' : (v - z) 0 * secondFundamental X (N p) p 0 j +
        (v - z) 1 * secondFundamental X (N p) p 1 j = 0 := by linarith
    simpa only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.transpose_apply,
      Pi.zero_apply, mul_comm] using hj'
  have hdetT : (secondFundamental X (N p) p).transpose.det ≠ 0 := by
    rwa [Matrix.det_transpose]
  have he : ((secondFundamental X (N p) p).transpose)⁻¹ *ᵥ
      ((secondFundamental X (N p) p).transpose *ᵥ (v - z)) = v - z := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdetT), Matrix.one_mulVec]
  rw [hzero, Matrix.mulVec_zero] at he
  exact sub_eq_zero.mp he.symm

theorem gaussMap_differential_injective {g : MetricField} {X N : Coord → Ambient} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hX : IsometricOn g X U) (hN : ContDiffOn ℝ ∞ N U)
    (hU : IsOpen U) (hn : ∀ q ∈ U, IsUnitNormalAt X (N q) q)
    {p : Coord} (hp : p ∈ U) (hK : gaussianCurvature g p ≠ 0) :
    Function.Injective (fderiv ℝ N p) := by
  apply gaussMap_differential_injective_of_second_form hX.1 hN hU hn hp
  intro hdet
  apply hK
  rw [curvature_eq_second_form_det_div_metric_det hg hX hU hp (hn p hp), hdet, zero_div]

end
end TightVer401
