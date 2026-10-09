import TightVer401.PolarSaddleSignCalculus
import TightVer401.PlanarSupportCurvature

/-! ver500 polar saddle criterion, for actual Cartesian Hessians and curvature.
This is a local calculus refinement; it does not assert radial filling existence. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Matrix
set_option backward.isDefEq.respectTransparency false

/-- Opposite signs of the two diagonal entries force a saddle, for any mixed entry. -/
theorem polarSymmetricMatrix_det_neg {a b c : ℝ} (ha : a < 0) (hc : 0 < c) :
    (seamSecondJet a b c).det < 0 := by
  rw [seamSecondJet_det]
  have h := mul_neg_of_neg_of_pos ha hc
  nlinarith [sq_nonneg b]

/-- The connection terms are computed from the actual polar chart differential.
In the coordinate basis the angular diagonal is f_θθ+r f_r, and the
mixed entry is f_rθ−f_θ/r. -/
theorem saddlePolarChart_correctedHessian {F : Coord → ℝ}
    (hF : ContDiff ℝ ∞ F) {p : Coord} (hr : p 0 ≠ 0) :
    seamCorrectedHessian saddlePolarChart (fun q => F (saddlePolarChart q)) p =
      !![planarHessian (fun q => F (saddlePolarChart q)) p 0 0,
          planarHessian (fun q => F (saddlePolarChart q)) p 0 1 -
            coordPartial 1 (fun q => F (saddlePolarChart q)) p / p 0;
         planarHessian (fun q => F (saddlePolarChart q)) p 1 0 -
            coordPartial 1 (fun q => F (saddlePolarChart q)) p / p 0,
          planarHessian (fun q => F (saddlePolarChart q)) p 1 1 +
            p 0 * coordPartial 0 (fun q => F (saddlePolarChart q)) p] := by
  have hJ : (seamCoordinateJacobian saddlePolarChart p).det ≠ 0 := by
    rwa [saddlePolarChart_jacobian_det]
  ext i j
  unfold seamCorrectedHessian
  rw [seamChartConnection_gradient_comp hF saddlePolarChart_contDiff hJ]
  simp only [seam_coordPartial_comp hF saddlePolarChart_contDiff,
    saddlePolarChart_coordPartial, saddlePolarChart_hessian, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp
  all_goals field_simp [hr] <;> ring

/-- The actual Cartesian Hessian determinant is the polar expression divided
by r²; the arbitrary mixed derivative enters only as a negative square. -/
theorem saddlePolarChart_hessian_det {F : Coord → ℝ}
    (hF : ContDiff ℝ ∞ F) {p : Coord} (hr : p 0 ≠ 0) :
    (planarHessian F (saddlePolarChart p)).det =
      (planarHessian (fun q => F (saddlePolarChart q)) p 0 0 *
          (planarHessian (fun q => F (saddlePolarChart q)) p 1 1 +
            p 0 * coordPartial 0 (fun q => F (saddlePolarChart q)) p) -
        (planarHessian (fun q => F (saddlePolarChart q)) p 0 1 -
          coordPartial 1 (fun q => F (saddlePolarChart q)) p / p 0)^2) / p 0^2 := by
  have hJ : (seamCoordinateJacobian saddlePolarChart p).det ≠ 0 := by
    rwa [saddlePolarChart_jacobian_det]
  have hd := seamCorrectedHessian_comp_det hF saddlePolarChart_contDiff hJ
  rw [saddlePolarChart_correctedHessian hF hr, saddlePolarChart_jacobian_det,
    Matrix.det_fin_two] at hd
  have hsym := planarHessian_symm (hF.comp saddlePolarChart_contDiff).contDiffOn
    isOpen_univ (mem_univ p) 1 0
  change planarHessian (fun q => F (saddlePolarChart q)) p 1 0 =
    planarHessian (fun q => F (saddlePolarChart q)) p 0 1 at hsym
  change planarHessian (fun q => F (saddlePolarChart q)) p 0 0 *
    (planarHessian (fun q => F (saddlePolarChart q)) p 1 1 +
      p 0 * coordPartial 0 (fun q => F (saddlePolarChart q)) p) -
    (planarHessian (fun q => F (saddlePolarChart q)) p 0 1 -
      coordPartial 1 (fun q => F (saddlePolarChart q)) p / p 0) *
    (planarHessian (fun q => F (saddlePolarChart q)) p 1 0 -
      coordPartial 1 (fun q => F (saddlePolarChart q)) p / p 0) =
    p 0^2 * (planarHessian F (saddlePolarChart p)).det at hd
  rw [hsym] at hd
  apply (eq_div_iff (pow_ne_zero 2 hr)).mpr
  nlinarith [hd]

/-- Actual polar derivatives imply the saddle sign for the Cartesian potential. -/
theorem saddlePolarChart_hessian_det_neg {F : Coord → ℝ}
    (hF : ContDiff ℝ ∞ F) {p : Coord} (hr : 0 < p 0)
    (hrr : planarHessian (fun q => F (saddlePolarChart q)) p 0 0 < 0)
    (hangular : 0 < planarHessian (fun q => F (saddlePolarChart q)) p 1 1 +
      p 0 * coordPartial 0 (fun q => F (saddlePolarChart q)) p) :
    (planarHessian F (saddlePolarChart p)).det < 0 := by
  rw [saddlePolarChart_hessian_det hF hr.ne']
  apply div_neg_of_neg_of_pos _ (sq_pos_of_ne_zero hr.ne')
  have hm := mul_neg_of_neg_of_pos hrr hangular
  nlinarith [sq_nonneg (planarHessian (fun q => F (saddlePolarChart q)) p 0 1 -
    coordPartial 1 (fun q => F (saddlePolarChart q)) p / p 0)]

/-- The sign is also intrinsic negative Gaussian curvature of the actual
support immersion, using the audited OpenAI induced metric. -/
theorem saddlePolarChart_gaussianCurvature_neg {F : Coord → ℝ}
    (hF : ContDiff ℝ ∞ F) {p : Coord} (hr : 0 < p 0)
    (hrr : planarHessian (fun q => F (saddlePolarChart q)) p 0 0 < 0)
    (hangular : 0 < planarHessian (fun q => F (saddlePolarChart q)) p 1 1 +
      p 0 * coordPartial 0 (fun q => F (saddlePolarChart q)) p) :
    gaussianCurvature (inducedMetric (planarSupportMap F)) (saddlePolarChart p) < 0 := by
  have hd := saddlePolarChart_hessian_det_neg hF hr hrr hangular
  exact (planarSupportMap_negative_curvature_iff hF.contDiffOn
    isOpen_univ (mem_univ (saddlePolarChart p)) hd.ne).mpr hd

end
end TightVer401
