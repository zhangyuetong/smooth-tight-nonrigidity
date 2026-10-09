import TightVer401.GaussTightnessHeightHessian
import TightVer401.GaussTightnessCriticalNormal
import TightVer401.GaussTightnessDifferential
import TightVer401.GaussTightnessDefiniteSign

/-! A regular unit-normal direction at a local height maximum has strictly
positive actual intrinsic curvature. Both signs of the given unit normal
are retained. Final consumer: `classicalPositiveGaussTightness_proved`. -/

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

/-- Negating the actual height direction negates the actual second form. -/
theorem gaussTightness_secondFundamental_neg (F : Coord → Ambient) (n : Ambient)
    (p : Coord) : secondFundamental F (-n) p = -secondFundamental F n p := by
  ext i j
  simp [secondFundamental]

/-- The necessary second derivative condition at an actual height maximum,
packaged as negative semidefiniteness of the actual second form. -/
theorem gaussTightness_localMax_height_neg_secondForm_posSemidef
    {F : Coord → Ambient} {U : Set Coord} (hF : ContDiffOn ℝ ∞ F U)
    (hU : IsOpen U) {p : Coord} (hp : p ∈ U) (w : Ambient)
    (hmax : IsLocalMax (height F w) p) :
    (-secondFundamental F w p).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · show (-secondFundamental F w p).conjTranspose = -secondFundamental F w p
    ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, Pi.neg_apply]
    change -inner ℝ (coordPartial j (coordPartial i F) p) w =
      -inner ℝ (coordPartial i (coordPartial j F) p) w
    rw [coordPartial_comm hF hU hp j i]
  · intro v
    have hle := gaussTightness_localMax_height_secondForm_nonpos hF hU hp w hmax v
    simpa only [star_trivial, Matrix.neg_mulVec, dotProduct_neg] using neg_nonneg.mpr hle

/-- A local height maximum with nondegenerate actual second form has
strictly positive intrinsic curvature, with the SAME actual metric. -/
theorem gaussTightness_localMax_curvature_pos_of_second_form_det
    {g : MetricField} {F : Coord → Ambient} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U)
    (hU : IsOpen U) {p : Coord} (hp : p ∈ U) (w : Ambient)
    (hn : IsUnitNormalAt F w p) (hmax : IsLocalMax (height F w) p)
    (hdet : (secondFundamental F w p).det ≠ 0) :
    0 < gaussianCurvature g p := by
  have hdetpos := real_two_matrix_det_pos_of_neg_posSemidef_of_ne_zero
    (secondFundamental F w p)
    (gaussTightness_localMax_height_neg_secondForm_posSemidef hF.1 hU hp w hmax) hdet
  rw [curvature_eq_second_form_det_div_metric_det hg hF hU hp hn]
  exact div_pos hdetpos (hg.2 p hp).det_pos

/-- At a local height maximum in a unit direction, injectivity of the
actual normal differential forces strictly positive actual curvature.
The height direction may be EITHER sign of the given normal. -/
theorem gaussTightness_localMax_curvature_pos_of_normal_injective
    {g : MetricField} {F N : Coord → Ambient} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U)
    (hN : ContDiffOn ℝ ∞ N U) (hU : IsOpen U)
    (hn : ∀ q ∈ U, IsUnitNormalAt F (N q) q)
    {p : Coord} (hp : p ∈ U) (w : Ambient) (hw : inner ℝ w w = 1)
    (hmax : IsLocalMax (height F w) p)
    (hiN : Function.Injective (fderiv ℝ N p)) :
    0 < gaussianCurvature g p := by
  have hdF : DifferentiableAt ℝ F p :=
    ((hF.1 p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hiF := isometricOn_injective_differential hg hF hp
  have hdetN := gaussTightness_second_form_det_ne_zero_of_normal_injective
    hF.1 hN hU hn hp hiF hiN
  have hsign := gaussTightness_localMax_height_normal_eq_or_neg_of_injective
    hdF hiF (N p) w (hn p hp) hw hmax
  have hdetw : (secondFundamental F w p).det ≠ 0 := by
    rcases hsign with hwN | hwN
    · rwa [hwN]
    · rwa [hwN, gaussTightness_secondFundamental_neg, real_two_matrix_det_neg]
  have hnw : IsUnitNormalAt F w p :=
    ⟨hw, gaussTightness_localMax_height_orthogonal hdF w hmax⟩
  exact gaussTightness_localMax_curvature_pos_of_second_form_det hg hF hU hp w hnw hmax hdetw

end
end TightVer401
