import TightVer401.GaussMapDifferential

/-! Converse Gauss-map regularity for the SAME actual immersed surface and
its actual unit normal. Final consumer: the regular-height argument in
`classicalPositiveGaussTightness_proved`. -/

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

/-- A vector in the kernel of the transposed actual second form is in the
kernel of the actual normal differential. -/
theorem gaussTightness_normal_differential_zero_of_second_form
    {X N : Coord → Ambient} {U : Set Coord}
    (hX : ContDiffOn ℝ ∞ X U) (hN : ContDiffOn ℝ ∞ N U) (hU : IsOpen U)
    (hn : ∀ q ∈ U, IsUnitNormalAt X (N q) q) {p : Coord} (hp : p ∈ U)
    (hiX : Function.Injective (fderiv ℝ X p)) (v : Coord)
    (hv : (secondFundamental X (N p) p).transpose *ᵥ v = 0) :
    fderiv ℝ N p v = 0 := by
  have ht : LinearIndependent ℝ (fun i : Fin 2 => coordPartial i X p) := by
    simpa only [Function.comp_def, Pi.basisFun_apply, coordPartial,
      ContinuousLinearMap.coe_coe] using
      (Pi.basisFun ℝ (Fin 2)).linearIndependent.map' (fderiv ℝ X p).toLinearMap
        (LinearMap.ker_eq_bot_of_injective hiX)
  have hwt (j : Fin 2) : inner ℝ (coordPartial j X p) (fderiv ℝ N p v) = 0 := by
    have hj := congrFun hv j
    have hj' : v 0 * secondFundamental X (N p) p 0 j +
        v 1 * secondFundamental X (N p) p 1 j = 0 := by
      simpa only [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Matrix.transpose_apply, Pi.zero_apply, mul_comm] using hj
    rw [real_inner_comm, fderiv_two_coordinates, inner_add_left,
      real_inner_smul_left, real_inner_smul_left,
      gaussMap_partial_pairing hX hN hU hn hp 0 j,
      gaussMap_partial_pairing hX hN hU hn hp 1 j]
    linarith
  have horth : inner ℝ (N p) (fderiv ℝ N p v) = 0 := by
    rw [real_inner_comm]
    exact sphere_differential_orthogonal hN hU hp (fun q hq => (hn q hq).1) v
  have heq := normal_eq_inner_smul_of_independent_tangents
    (fun i => coordPartial i X p) ht (N p) (fderiv ℝ N p v)
    (hn p hp).1 (fun i => (hn p hp).2 (Pi.single i 1)) hwt
  simpa only [horth, zero_smul] using heq

/-- Injectivity of the actual normal differential forces the actual
second fundamental determinant to be nonzero. -/
theorem gaussTightness_second_form_det_ne_zero_of_normal_injective
    {X N : Coord → Ambient} {U : Set Coord}
    (hX : ContDiffOn ℝ ∞ X U) (hN : ContDiffOn ℝ ∞ N U) (hU : IsOpen U)
    (hn : ∀ q ∈ U, IsUnitNormalAt X (N q) q) {p : Coord} (hp : p ∈ U)
    (hiX : Function.Injective (fderiv ℝ X p))
    (hiN : Function.Injective (fderiv ℝ N p)) :
    (secondFundamental X (N p) p).det ≠ 0 := by
  have hiB : Function.Injective (secondFundamental X (N p) p).transpose.mulVec := by
    intro v z hvz
    have hz : (secondFundamental X (N p) p).transpose *ᵥ (v - z) = 0 := by
      rw [Matrix.mulVec_sub, hvz, sub_self]
    have hd := gaussTightness_normal_differential_zero_of_second_form
      hX hN hU hn hp hiX (v - z) hz
    have he : v - z = 0 := hiN (by simpa only [map_zero] using hd)
    exact sub_eq_zero.mp he
  have hu := Matrix.mulVec_injective_iff_isUnit.mp hiB
  have hd : (secondFundamental X (N p) p).transpose.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
  simpa only [Matrix.det_transpose] using hd

/-- Converse to `gaussMap_differential_injective`, for the same actual
isometric surface and normal. -/
theorem gaussTightness_curvature_ne_zero_of_normal_injective
    {g : MetricField} {X N : Coord → Ambient} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hX : IsometricOn g X U)
    (hN : ContDiffOn ℝ ∞ N U) (hU : IsOpen U)
    (hn : ∀ q ∈ U, IsUnitNormalAt X (N q) q)
    {p : Coord} (hp : p ∈ U) (hiN : Function.Injective (fderiv ℝ N p)) :
    gaussianCurvature g p ≠ 0 := by
  have hd := gaussTightness_second_form_det_ne_zero_of_normal_injective
    hX.1 hN hU hn hp (isometricOn_injective_differential hg hX hp) hiN
  rw [curvature_eq_second_form_det_div_metric_det hg hX hU hp (hn p hp)]
  exact div_ne_zero hd (metricDet_ne_zero hg hp)

/-- Actual Gauss differential regularity is equivalent to nonzero
intrinsic Gaussian curvature. -/
theorem gaussTightness_normal_injective_iff_curvature_ne_zero
    {g : MetricField} {X N : Coord → Ambient} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hX : IsometricOn g X U)
    (hN : ContDiffOn ℝ ∞ N U) (hU : IsOpen U)
    (hn : ∀ q ∈ U, IsUnitNormalAt X (N q) q) {p : Coord} (hp : p ∈ U) :
    Function.Injective (fderiv ℝ N p) ↔ gaussianCurvature g p ≠ 0 :=
  ⟨gaussTightness_curvature_ne_zero_of_normal_injective hg hX hN hU hn hp,
    gaussMap_differential_injective hg hX hN hU hn hp⟩

end
end TightVer401
