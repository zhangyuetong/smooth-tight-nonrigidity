import TightVer401.GaussTightnessMaximumCurvature

/-! Actual second-form trace signs at regular height maxima. These signs
distinguish the two possible unit-normal directions for the SAME surface.
Final consumer: the positive-region Gauss-injectivity uniqueness argument
in `classicalPositiveGaussTightness_proved`. -/

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

/-- Symmetry of the actual coordinate second form follows from the
commuting actual second coordinate derivatives. -/
theorem gaussTightness_secondFundamental_isSymm
    {F : Coord → Ambient} {U : Set Coord} (hF : ContDiffOn ℝ ∞ F U)
    (hU : IsOpen U) {p : Coord} (hp : p ∈ U) (w : Ambient) :
    (secondFundamental F w p).IsSymm := by
  apply Matrix.IsSymm.ext_iff.mpr
  intro i j
  change inner ℝ (coordPartial j (coordPartial i F) p) w =
    inner ℝ (coordPartial i (coordPartial j F) p) w
  rw [coordPartial_comm hF hU hp j i]

/-- The height-direction second form has strictly negative trace at a
local height maximum whenever its determinant is strictly positive. -/
theorem gaussTightness_localMax_height_secondForm_trace_neg
    {F : Coord → Ambient} {U : Set Coord} (hF : ContDiffOn ℝ ∞ F U)
    (hU : IsOpen U) {p : Coord} (hp : p ∈ U) (w : Ambient)
    (hmax : IsLocalMax (height F w) p)
    (hdet : 0 < (secondFundamental F w p).det) :
    (secondFundamental F w p).trace < 0 := by
  have hdiag (i : Fin 2) : secondFundamental F w p i i ≤ 0 := by
    have hle := gaussTightness_localMax_height_secondForm_nonpos hF hU hp w hmax
      (Pi.single i 1)
    simpa only [Matrix.mulVec_single_one, single_dotProduct, one_mul, Matrix.col_apply] using hle
  have hle : (secondFundamental F w p).trace ≤ 0 := by
    rw [Matrix.trace_fin_two]
    exact add_nonpos (hdiag 0) (hdiag 1)
  have hne := real_two_matrix_trace_ne_zero_of_det_pos
    (secondFundamental F w p) (gaussTightness_secondFundamental_isSymm hF hU hp w) hdet
  exact lt_of_le_of_ne hle hne

/-- At a regular local height maximum in a unit direction, positive
trace of the given-normal second form characterizes the opposite-normal
height direction, and negative trace characterizes the same direction. -/
theorem gaussTightness_localMax_height_normal_trace_sign
    {F : Coord → Ambient} {U : Set Coord} (hF : ContDiffOn ℝ ∞ F U)
    (hU : IsOpen U) {p : Coord} (hp : p ∈ U)
    (hiF : Function.Injective (fderiv ℝ F p)) (n w : Ambient)
    (hn : IsUnitNormalAt F n p) (hw : inner ℝ w w = 1)
    (hmax : IsLocalMax (height F w) p)
    (hdet : 0 < (secondFundamental F n p).det) :
    (0 < (secondFundamental F n p).trace ↔ w = -n) ∧
      ((secondFundamental F n p).trace < 0 ↔ w = n) := by
  have hdF : DifferentiableAt ℝ F p :=
    ((hF p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hsign := gaussTightness_localMax_height_normal_eq_or_neg_of_injective
    hdF hiF n w hn hw hmax
  have hdetw : 0 < (secondFundamental F w p).det := by
    rcases hsign with hsame | hopp
    · simpa only [hsame] using hdet
    · simpa only [hopp, gaussTightness_secondFundamental_neg,
        real_two_matrix_det_neg] using hdet
  have htracew := gaussTightness_localMax_height_secondForm_trace_neg hF hU hp w hmax hdetw
  have hsameNeg (hsame : w = n) : (secondFundamental F n p).trace < 0 := by
    simpa only [hsame] using htracew
  have hoppPos (hopp : w = -n) : 0 < (secondFundamental F n p).trace := by
    have ht : -(secondFundamental F n p).trace < 0 := by
      simpa only [hopp, gaussTightness_secondFundamental_neg, Matrix.trace_neg] using htracew
    linarith
  constructor
  · constructor
    · intro hpos
      rcases hsign with hsame | hopp
      · exact False.elim ((not_lt_of_gt (hsameNeg hsame)) hpos)
      · exact hopp
    · exact hoppPos
  · constructor
    · intro hneg
      rcases hsign with hsame | hopp
      · exact hsame
      · exact False.elim ((not_lt_of_gt (hoppPos hopp)) hneg)
    · exact hsameNeg

/-- Direct sign characterization under actual normal differential
regularity and the SAME actual isometric immersion. -/
theorem gaussTightness_localMax_normal_trace_sign_of_normal_injective
    {g : MetricField} {F N : Coord → Ambient} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U)
    (hN : ContDiffOn ℝ ∞ N U) (hU : IsOpen U)
    (hn : ∀ q ∈ U, IsUnitNormalAt F (N q) q) {p : Coord} (hp : p ∈ U)
    (w : Ambient) (hw : inner ℝ w w = 1) (hmax : IsLocalMax (height F w) p)
    (hiN : Function.Injective (fderiv ℝ N p)) :
    (0 < (secondFundamental F (N p) p).trace ↔ w = -(N p)) ∧
      ((secondFundamental F (N p) p).trace < 0 ↔ w = N p) := by
  have hK := gaussTightness_localMax_curvature_pos_of_normal_injective
    hg hF hN hU hn hp w hw hmax hiN
  have hdet : 0 < (secondFundamental F (N p) p).det := by
    rw [det_secondFundamental_eq_gaussianCurvature_mul_det hg hF hU hp (hn p hp)]
    exact mul_pos hK (hg.2 p hp).det_pos
  exact gaussTightness_localMax_height_normal_trace_sign hF.1 hU hp
    (isometricOn_injective_differential hg hF hp) (N p) w (hn p hp) hw hmax hdet

end
end TightVer401
