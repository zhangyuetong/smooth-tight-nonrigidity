import TightVer401.PlanarSupportSecondForm
import TightVer401.PlanarSupportRegularity

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix

theorem planarHessian_det_contDiffOn {G : Coord → ℝ} {U : Set Coord}
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (fun p => (planarHessian G p).det) U := by
  have hA (i j : Fin 2) : ContDiffOn ℝ ∞ (fun p => planarHessian G p i j) U :=
    partial_contDiffOn (partial_contDiffOn hG hU j) hU i
  simpa only [Matrix.det_fin_two] using ((hA 0 0).mul (hA 1 1)).sub
    ((hA 0 1).mul (hA 1 0))

theorem planarSupportMap_gaussianCurvature {G : Coord → ℝ} {U : Set Coord}
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U)
    (hdet : ∀ q ∈ U, (planarHessian G q).det ≠ 0) {p : Coord} (hp : p ∈ U) :
    gaussianCurvature (inducedMetric (planarSupportMap G)) p =
      1 / (planarWeight p ^ 4 * (planarHessian G p).det) := by
  have hX := planarSupportMap_contDiffOn hG hU
  have hg := planarSupportMap_metric_smoothPositiveOn hG hU hdet
  rw [curvature_eq_second_form_det_div_metric_det hg (inducedMetric_isometricOn hX)
    hU hp (planarSupportMap_isUnitNormal hG hU hp),
    planarSupportMap_secondFundamental hG hU hp, planarSupportMap_metric_det hG hU hp,
    Matrix.det_smul]
  simp only [Fintype.card_fin]
  field_simp [ne_of_gt (planarWeight_pos p), hdet p hp]
  <;> ring

theorem planarSupportMap_gaussianCurvature_at {G : Coord → ℝ} {U : Set Coord}
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U)
    (hdet : (planarHessian G p).det ≠ 0) :
    gaussianCurvature (inducedMetric (planarSupportMap G)) p =
      1 / (planarWeight p ^ 4 * (planarHessian G p).det) := by
  let V := U ∩ (fun q => (planarHessian G q).det) ⁻¹' ({0}ᶜ : Set ℝ)
  have hV : IsOpen V :=
    (planarHessian_det_contDiffOn hG hU).continuousOn.isOpen_inter_preimage hU
      (isClosed_singleton.isOpen_compl)
  have hpV : p ∈ V := ⟨hp, hdet⟩
  exact planarSupportMap_gaussianCurvature (hG.mono inter_subset_left) hV
    (fun q hq => hq.2) hpV

theorem planarSupportMap_negative_curvature_iff {G : Coord → ℝ} {U : Set Coord}
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U)
    (hdet : (planarHessian G p).det ≠ 0) :
    gaussianCurvature (inducedMetric (planarSupportMap G)) p < 0 ↔
      (planarHessian G p).det < 0 := by
  rw [planarSupportMap_gaussianCurvature_at hG hU hp hdet]
  have hw4 : 0 < planarWeight p ^ 4 := pow_pos (planarWeight_pos p) 4
  simp [div_neg_iff, mul_neg_iff, hw4, not_lt_of_ge hw4.le]

end
end TightVer401
