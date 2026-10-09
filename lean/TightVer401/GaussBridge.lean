import OAI.Geometry.IsometricImmersion.Curvature.GaussEquation
import OAI.Geometry.IsometricImmersion.Curvature.IntrinsicCurvature
import Mathlib.Analysis.Matrix.PosDef

/-! The curvature convention needed by ver401, derived from OpenAI's Gauss equation. -/
namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff

theorem curvature_eq_second_form_det_div_metric_det
    {g : MetricField} {X : Coord → Ambient} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hX : IsometricOn g X U) (hU : IsOpen U)
    {p : Coord} (hp : p ∈ U) {n : Ambient} (hn : IsUnitNormalAt X n p) :
    gaussianCurvature g p = (secondFundamental X n p).det / (g p).det := by
  rw [det_secondFundamental_eq_gaussianCurvature_mul_det hg hX hU hp hn,
    mul_div_cancel_right₀ _ (metricDet_ne_zero hg hp)]

theorem negative_curvature_iff_second_form_det_neg
    {g : MetricField} {X : Coord → Ambient} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hX : IsometricOn g X U) (hU : IsOpen U)
    {p : Coord} (hp : p ∈ U) {n : Ambient} (hn : IsUnitNormalAt X n p) :
    gaussianCurvature g p < 0 ↔ (secondFundamental X n p).det < 0 := by
  rw [curvature_eq_second_form_det_div_metric_det hg hX hU hp hn]
  rw [div_lt_iff₀ (hg.2 p hp).det_pos, zero_mul]

end
end TightVer401
