import TightVer401.PlanarSupportForms

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix

private theorem planarSupportMap_contDiffOn {G : Coord → ℝ} {U : Set Coord}
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (planarSupportMap G) U := by
  have ha := partial_contDiffOn hG hU 0
  have hb := partial_contDiffOn hG hU 1
  have hD : ContDiffOn ℝ ∞
      (fun p : Coord => G p - p 0 * coordPartial 0 G p - p 1 * coordPartial 1 G p) U :=
    (hG.sub ((ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)).contDiff.contDiffOn.mul ha)).sub
      ((ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)).contDiff.contDiffOn.mul hb)
  have hΦ : ContDiffOn ℝ ∞
      (fun p : Coord => ![coordPartial 0 G p, coordPartial 1 G p,
        G p - p 0 * coordPartial 0 G p - p 1 * coordPartial 1 G p]) U := by
    apply contDiffOn_pi.mpr
    intro j
    fin_cases j
    · exact ha
    · exact hb
    · exact hD
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.contDiff.comp_contDiffOn hΦ

theorem planarSupportMap_differential_injective {G : Coord → ℝ} {U : Set Coord}
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U)
    (hdet : (planarHessian G p).det ≠ 0) :
    Function.Injective (fderiv ℝ (planarSupportMap G) p) := by
  intro v w hvw
  have hz : fderiv ℝ (planarSupportMap G) p (v - w) = 0 := by simp [map_sub, hvw]
  rw [fderiv_two_coordinates,
    planarSupportMap_coordPartial hG hU hp 0,
    planarSupportMap_coordPartial hG hU hp 1] at hz
  have hzero : (planarHessian G p).transpose *ᵥ (v - w) = 0 := by
    ext j
    have hj := congrArg (fun a : Ambient => a j.castSucc) hz
    fin_cases j <;>
      simpa [planarHessian, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Matrix.transpose_apply, mul_comm] using hj
  have hdetT : (planarHessian G p).transpose.det ≠ 0 := by
    simpa only [Matrix.det_transpose] using hdet
  have heq : ((planarHessian G p).transpose)⁻¹ *ᵥ
      ((planarHessian G p).transpose *ᵥ (v - w)) = v - w := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdetT),
      Matrix.one_mulVec]
  rw [hzero, Matrix.mulVec_zero] at heq
  exact sub_eq_zero.mp heq.symm

theorem planarSupportMap_metric_det {G : Coord → ℝ} {U : Set Coord}
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U) :
    (inducedMetric (planarSupportMap G) p).det =
      planarWeight p ^ 2 * (planarHessian G p).det ^ 2 := by
  rw [planarSupportMap_inducedMetric hG hU hp]
  have hmiddle : (1 + Matrix.of (fun i j : Fin 2 => p i * p j)).det = planarWeight p ^ 2 := by
    rw [planarWeight_sq, Matrix.det_fin_two]
    simp [Matrix.add_apply]
    ring
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hmiddle]
  ring

theorem planarSupportMap_metric_smoothPositiveOn {G : Coord → ℝ} {U : Set Coord}
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U)
    (hdet : ∀ p ∈ U, (planarHessian G p).det ≠ 0) :
    SmoothPositiveOn (inducedMetric (planarSupportMap G)) U :=
  inducedMetric_smoothPositiveOn (planarSupportMap_contDiffOn hG hU) hU
    (fun p hp => planarSupportMap_differential_injective hG hU hp (hdet p hp))

end
end TightVer401
