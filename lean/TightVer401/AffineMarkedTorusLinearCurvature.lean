import TightVer401.AffineMarkedTorusLinearNormals
import TightVer401.NativeProductPlaneCurvature

/-! Actual Gaussian curvature scaling for the literal marker of determinant
two. The actual Gram determinant is computed from the retained cross norm
identity and the retained one-dimensional normal-space decomposition.
The actual second form follows from the global height function identity.
The retained Gauss equation then gives K divided by 4 times the fourth
power of the inverse-transpose normal norm. All hypotheses are ordinary
local smoothness, actual differential injection and actual unit normality.
-/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped Matrix ContDiff Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false

private theorem affineLinear_metric_det_cross (X : Coord → Ambient) (p : Coord) :
    (inducedMetric X p).det = ‖ambientCross (coordPartial 0 X p) (coordPartial 1 X p)‖^2 := by
  simp only [inducedMetric, Matrix.det_fin_two]
  rw [ambientCross_norm_sq,
    real_inner_comm (coordPartial 1 X p) (coordPartial 0 X p)]
  ring

/-- The marked actual first form is scaled in determinant by 4 times the
squared inverse-transpose normal norm. This is not a metric equality. -/
theorem affineMarkedTorusLinear_metric_det {X : Coord → Ambient} {p : Coord}
    (hX : DifferentiableAt ℝ X p) (hi : Function.Injective (fderiv ℝ X p))
    {n : Ambient} (hn : IsUnitNormalAt X n p) :
    (inducedMetric (fun q => torusAffineMarker (X q)) p).det =
      4 * ‖torusAffineMarkerContra n‖^2 * (inducedMetric X p).det := by
  let a := coordPartial 0 X p
  let b := coordPartial 1 X p
  have ht : LinearIndependent ℝ (fun i : Fin 2 => coordPartial i X p) := by
    simpa only [Function.comp_def, Pi.basisFun_apply, coordPartial,
      ContinuousLinearMap.coe_coe] using
      (Pi.basisFun ℝ (Fin 2)).linearIndependent.map' (fderiv ℝ X p).toLinearMap
        (LinearMap.ker_eq_bot_of_injective hi)
  have hab : LinearIndependent ℝ ![a,b] := by
    convert! ht using 1
    funext i
    fin_cases i <;> rfl
  let α := inner ℝ n (ambientCross a b)
  have hc : ambientCross a b = α • n :=
    normal_eq_inner_smul_of_pair a b n (ambientCross a b) hab hn.1
      (hn.2 (Pi.single 0 1)) (hn.2 (Pi.single 1 1))
      (ambientCross_orthogonal_left a b) (ambientCross_orthogonal_right a b)
  have hnorm : ‖ambientCross a b‖^2 = α^2 := by
    rw [← real_inner_self_eq_norm_sq, hc, real_inner_smul_left,
      real_inner_smul_right, hn.1]
    ring
  have hdet : (inducedMetric X p).det = α^2 :=
    (affineLinear_metric_det_cross X p).trans hnorm
  rw [affineLinear_metric_det_cross,
    affineMarkedTorusLinear_coordPartial hX 0, affineMarkedTorusLinear_coordPartial hX 1]
  change ‖ambientCross (torusAffineMarker a) (torusAffineMarker b)‖^2 = _
  rw [affineMarkedTorusLinear_cross, hc, hdet]
  change ‖(2 : ℝ) • torusAffineMarkerContraLinearEquiv (α • n)‖^2 =
    4 * ‖torusAffineMarkerContra n‖^2 * α^2
  rw [map_smul, smul_smul, norm_smul]
  simp only [Real.norm_eq_abs, mul_pow, sq_abs, torusAffineMarkerContraLinearEquiv_apply]
  ring

private theorem affineLinear_partial_const_mul {f : Coord → ℝ} {p : Coord}
    (hf : DifferentiableAt ℝ f p) (c : ℝ) (i : Fin 2) :
    coordPartial i (fun q => c * f q) p = c * coordPartial i f p := by
  simp only [coordPartial, fderiv_const_mul hf, ContinuousLinearMap.smul_apply, smul_eq_mul]

private theorem affineLinear_second_const_mul {f : Coord → ℝ} {U : Set Coord}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) {p : Coord} (hp : p ∈ U)
    (c : ℝ) (i j : Fin 2) :
    coordPartial i (coordPartial j (fun q => c * f q)) p =
      c * coordPartial i (coordPartial j f) p := by
  have he : coordPartial j (fun q => c * f q) =ᶠ[𝓝 p]
      (fun q => c * coordPartial j f q) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact affineLinear_partial_const_mul
      (((hf q hq).contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp)) c j
  have hd : DifferentiableAt ℝ (coordPartial j f) p :=
    (((partial_contDiffOn hf hU j) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by simp)
  change fderiv ℝ (coordPartial j (fun q => c * f q)) p (Pi.single i 1) = _
  rw [he.fderiv_eq]
  exact affineLinear_partial_const_mul hd c i

/-- The actual normal second form scales by the reciprocal normal norm,
derived using the actual global height identity. -/
theorem affineMarkedTorusLinear_secondFundamental {X : Coord → Ambient} {U : Set Coord}
    (hU : IsOpen U) (hX : ContDiffOn ℝ ∞ X U) {p : Coord} (hp : p ∈ U) (n : Ambient) :
    secondFundamental (fun q => torusAffineMarker (X q)) (affineMarkedTorusLinearNormal n) p =
      (‖torusAffineMarkerContra n‖⁻¹ : ℝ) • secondFundamental X n p := by
  have hB : ContDiffOn ℝ ∞ (fun q => torusAffineMarker (X q)) U :=
    torusAffineMarkerLinearEquiv.contDiff.comp_contDiffOn hX
  have hH : height (fun q => torusAffineMarker (X q)) (affineMarkedTorusLinearNormal n) =
      (fun q => ‖torusAffineMarkerContra n‖⁻¹ * height X n q) := by
    rw [affineMarkedTorusLinear_height]
    funext q
    simp only [div_eq_mul_inv]
    ring
  ext i j
  calc
    secondFundamental (fun q => torusAffineMarker (X q)) (affineMarkedTorusLinearNormal n) p i j =
        coordPartial i (coordPartial j
          (height (fun q => torusAffineMarker (X q)) (affineMarkedTorusLinearNormal n))) p :=
      (second_partial_height hB hU hp (affineMarkedTorusLinearNormal n) i j).symm
    _ = ‖torusAffineMarkerContra n‖⁻¹ * coordPartial i (coordPartial j (height X n)) p := by
      rw [hH]
      exact affineLinear_second_const_mul hU (height_smooth hX n) hp _ i j
    _ = ((‖torusAffineMarkerContra n‖⁻¹ : ℝ) • secondFundamental X n p) i j := by
      exact congrArg (fun a : ℝ => ‖torusAffineMarkerContra n‖⁻¹ * a)
        (second_partial_height hX hU hp n i j)

/-- Exact actual affine curvature formula for the literal determinant-two
marker. It multiplies K by a strictly positive factor. -/
theorem affineMarkedTorusLinear_gaussianCurvature {X : Coord → Ambient} {U : Set Coord}
    (hU : IsOpen U) (hX : ContDiffOn ℝ ∞ X U)
    (hi : ∀ q ∈ U, Function.Injective (fderiv ℝ X q))
    {p : Coord} (hp : p ∈ U) {n : Ambient} (hn : IsUnitNormalAt X n p) :
    gaussianCurvature (inducedMetric (fun q => torusAffineMarker (X q))) p =
      gaussianCurvature (inducedMetric X) p / (4 * ‖torusAffineMarkerContra n‖^4) := by
  have hB : ContDiffOn ℝ ∞ (fun q => torusAffineMarker (X q)) U :=
    torusAffineMarkerLinearEquiv.contDiff.comp_contDiffOn hX
  have hd : DifferentiableAt ℝ X p :=
    ((hX p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hiB : ∀ q ∈ U, Function.Injective
      (fderiv ℝ (fun z => torusAffineMarker (X z)) q) := by
    intro q hq v w he
    rw [affineMarkedTorusLinear_fderiv
      (((hX q hq).contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp))] at he
    change torusAffineMarker (fderiv ℝ X q v) = torusAffineMarker (fderiv ℝ X q w) at he
    exact hi q hq (torusAffineMarker_injective he)
  have hg := inducedMetric_smoothPositiveOn hX hU hi
  have hgB := inducedMetric_smoothPositiveOn hB hU hiB
  have hnB := affineMarkedTorusLinear_isUnitNormalAt hd hn
  have hc : ‖torusAffineMarkerContra n‖ ≠ 0 :=
    (affineMarkedTorusLinearNormal_scale_pos hn.1).ne'
  rw [curvature_eq_second_form_det_div_metric_det hgB (inducedMetric_isometricOn hB)
      hU hp hnB,
    curvature_eq_second_form_det_div_metric_det hg (inducedMetric_isometricOn hX) hU hp hn,
    affineMarkedTorusLinear_secondFundamental hU hX hp n,
    Matrix.det_smul, affineMarkedTorusLinear_metric_det hd (hi p hp) hn]
  simp only [Fintype.card_fin]
  field_simp [hc, metricDet_ne_zero hg hp] <;> ring

theorem affineMarkedTorusLinear_gaussianCurvature_pos_iff
    {X : Coord → Ambient} {U : Set Coord} (hU : IsOpen U) (hX : ContDiffOn ℝ ∞ X U)
    (hi : ∀ q ∈ U, Function.Injective (fderiv ℝ X q)) {p : Coord} (hp : p ∈ U)
    {n : Ambient} (hn : IsUnitNormalAt X n p) :
    0 < gaussianCurvature (inducedMetric (fun q => torusAffineMarker (X q))) p ↔
      0 < gaussianCurvature (inducedMetric X) p := by
  rw [affineMarkedTorusLinear_gaussianCurvature hU hX hi hp hn]
  have hden : 0 < 4 * ‖torusAffineMarkerContra n‖^4 := by
    exact mul_pos (by norm_num) (pow_pos (affineMarkedTorusLinearNormal_scale_pos hn.1) _)
  exact div_pos_iff_of_pos_right hden

theorem affineMarkedTorusLinear_gaussianCurvature_neg_iff
    {X : Coord → Ambient} {U : Set Coord} (hU : IsOpen U) (hX : ContDiffOn ℝ ∞ X U)
    (hi : ∀ q ∈ U, Function.Injective (fderiv ℝ X q)) {p : Coord} (hp : p ∈ U)
    {n : Ambient} (hn : IsUnitNormalAt X n p) :
    gaussianCurvature (inducedMetric (fun q => torusAffineMarker (X q))) p < 0 ↔
      gaussianCurvature (inducedMetric X) p < 0 := by
  rw [affineMarkedTorusLinear_gaussianCurvature hU hX hi hp hn]
  have hden : 0 < 4 * ‖torusAffineMarkerContra n‖^4 :=
    mul_pos (by norm_num) (pow_pos (affineMarkedTorusLinearNormal_scale_pos hn.1) _)
  rw [div_lt_iff₀ hden, zero_mul]

theorem affineMarkedTorusLinear_gaussianCurvature_eq_zero_iff
    {X : Coord → Ambient} {U : Set Coord} (hU : IsOpen U) (hX : ContDiffOn ℝ ∞ X U)
    (hi : ∀ q ∈ U, Function.Injective (fderiv ℝ X q)) {p : Coord} (hp : p ∈ U)
    {n : Ambient} (hn : IsUnitNormalAt X n p) :
    gaussianCurvature (inducedMetric (fun q => torusAffineMarker (X q))) p = 0 ↔
      gaussianCurvature (inducedMetric X) p = 0 := by
  rw [affineMarkedTorusLinear_gaussianCurvature hU hX hi hp hn, div_eq_zero_iff]
  have hden : 4 * ‖torusAffineMarkerContra n‖^4 ≠ 0 :=
    (mul_pos (by norm_num) (pow_pos (affineMarkedTorusLinearNormal_scale_pos hn.1) _)).ne'
  simp only [hden, or_false]

end
end TightVer401
