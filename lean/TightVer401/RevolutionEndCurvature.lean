import TightVer401.RevolutionEndSecondForm

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Matrix
set_option backward.isDefEq.respectTransparency false

theorem revolutionEnd_metric_det {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q) (p : Coord) :
    (inducedMetric (revolutionEnd q) p).det = q (p 1)^2 * (1 + deriv q (p 1)^2) := by
  rw [revolutionEnd_metric hq p, Matrix.det_fin_two]
  simp

theorem revolutionEnd_secondForm_det {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q) (p : Coord) :
    (secondFundamental (revolutionEnd q) (revolutionEndNormal q p) p).det =
      -q (p 1) * deriv (deriv q) (p 1) / revolutionWeight (deriv q (p 1))^2 := by
  rw [revolutionEnd_secondFundamental hq p, Matrix.det_fin_two]
  simp
  ring

theorem revolutionEnd_gaussianCurvature {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    {p : Coord} (hqp : 0 < q (p 1)) :
    gaussianCurvature (inducedMetric (revolutionEnd q)) p =
      -deriv (deriv q) (p 1) / (q (p 1) * (1 + deriv q (p 1)^2)^2) := by
  let U : Set Coord := {z | 0 < q (z 1)}
  have hU : IsOpen U := isOpen_lt continuous_const (hq.continuous.comp (continuous_apply 1))
  have hX := (revolutionEnd_contDiff hq).contDiffOn (s := U)
  have hg := inducedMetric_smoothPositiveOn hX hU
    (fun z hz => revolutionEnd_differential_injective hq (ne_of_gt hz))
  rw [curvature_eq_second_form_det_div_metric_det hg (inducedMetric_isometricOn hX)
    hU hqp (revolutionEnd_isUnitNormal hq p), revolutionEnd_secondForm_det hq p,
    revolutionEnd_metric_det hq p, revolutionWeight_sq]
  have henergy : 1 + deriv q (p 1)^2 ≠ 0 := ne_of_gt (by positivity : 0 < 1 + deriv q (p 1)^2)
  field_simp [ne_of_gt hqp, henergy]
  <;> ring

theorem revolutionEnd_gaussianCurvature_neg {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    {p : Coord} (hqp : 0 < q (p 1)) (hconvex : 0 < deriv (deriv q) (p 1)) :
    gaussianCurvature (inducedMetric (revolutionEnd q)) p < 0 := by
  rw [revolutionEnd_gaussianCurvature hq hqp]
  apply div_neg_of_neg_of_pos (neg_neg_of_pos hconvex)
  exact mul_pos hqp (sq_pos_of_pos (by positivity))

end
end TightVer401
