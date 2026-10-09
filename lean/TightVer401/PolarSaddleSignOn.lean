import TightVer401.PolarSaddleSignLocal

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Actual polar Hessian formula for a potential on an open source domain. -/
theorem saddlePolarChart_correctedHessian_on {F : Coord → ℝ} {U : Set Coord}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    {p : Coord} (hp : saddlePolarChart p ∈ U) (hr : p 0 ≠ 0) :
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
  have hdiff := (hF.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have herror (i j : Fin 2) :
      (∑ a : Fin 2, coordPartial a F (saddlePolarChart p)*
        planarHessian (fun q => saddlePolarChart q a) p i j) =
      (if i = 0 ∧ j = 0 then 0 else if i = 1 ∧ j = 1 then
        -p 0 * coordPartial 0 (fun q => F (saddlePolarChart q)) p else
        coordPartial 1 (fun q => F (saddlePolarChart q)) p / p 0) := by
    simp only [polarLocal_coordPartial_comp hdiff saddlePolarChart_contDiff,
      saddlePolarChart_coordPartial, saddlePolarChart_hessian, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp
    all_goals field_simp [hr] <;> ring
  ext i j
  rw [polarLocal_correctedHessian_comp hF hU saddlePolarChart_contDiff hp hJ]
  have hh := polarLocal_planarHessian_comp hF hU saddlePolarChart_contDiff hp i j
  rw [herror] at hh
  fin_cases i <;> fin_cases j <;> simp at hh ⊢ <;> linarith

/-- Cartesian determinant from actual angular and radial derivatives on a
punctured open source; the arbitrary mixed entry contributes a negative square. -/
theorem saddlePolarChart_hessian_det_on {F : Coord → ℝ} {U : Set Coord}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    {p : Coord} (hp : saddlePolarChart p ∈ U) (hr : p 0 ≠ 0) :
    (planarHessian F (saddlePolarChart p)).det =
      (planarHessian (fun q => F (saddlePolarChart q)) p 0 0 *
          (planarHessian (fun q => F (saddlePolarChart q)) p 1 1 +
            p 0 * coordPartial 0 (fun q => F (saddlePolarChart q)) p) -
        (planarHessian (fun q => F (saddlePolarChart q)) p 0 1 -
          coordPartial 1 (fun q => F (saddlePolarChart q)) p / p 0)^2) / p 0^2 := by
  have hJ : (seamCoordinateJacobian saddlePolarChart p).det ≠ 0 := by
    rwa [saddlePolarChart_jacobian_det]
  have hd := congrArg Matrix.det
    (polarLocal_correctedHessian_comp hF hU saddlePolarChart_contDiff hp hJ)
  rw [saddlePolarChart_correctedHessian_on hF hU hp hr, Matrix.det_mul,
    Matrix.det_mul, Matrix.det_transpose, saddlePolarChart_jacobian_det,
    Matrix.det_fin_two] at hd
  have hpre : IsOpen (saddlePolarChart ⁻¹' U) := hU.preimage saddlePolarChart_contDiff.continuous
  have hcomp : ContDiffOn ℝ ∞ (fun q => F (saddlePolarChart q)) (saddlePolarChart ⁻¹' U) :=
    hF.comp saddlePolarChart_contDiff.contDiffOn (fun _ hq => hq)
  have hsym := planarHessian_symm hcomp hpre hp 1 0
  change planarHessian (fun q => F (saddlePolarChart q)) p 1 0 =
    planarHessian (fun q => F (saddlePolarChart q)) p 0 1 at hsym
  change planarHessian (fun q => F (saddlePolarChart q)) p 0 0 *
    (planarHessian (fun q => F (saddlePolarChart q)) p 1 1 +
      p 0 * coordPartial 0 (fun q => F (saddlePolarChart q)) p) -
    (planarHessian (fun q => F (saddlePolarChart q)) p 0 1 -
      coordPartial 1 (fun q => F (saddlePolarChart q)) p / p 0) *
    (planarHessian (fun q => F (saddlePolarChart q)) p 1 0 -
      coordPartial 1 (fun q => F (saddlePolarChart q)) p / p 0) =
    p 0 * (planarHessian F (saddlePolarChart p)).det * p 0 at hd
  rw [hsym] at hd
  apply (eq_div_iff (pow_ne_zero 2 hr)).mpr
  nlinarith [hd]

theorem saddlePolarChart_hessian_det_neg_on {F : Coord → ℝ} {U : Set Coord}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    {p : Coord} (hp : saddlePolarChart p ∈ U) (hr : 0 < p 0)
    (hrr : planarHessian (fun q => F (saddlePolarChart q)) p 0 0 < 0)
    (hangular : 0 < planarHessian (fun q => F (saddlePolarChart q)) p 1 1 +
      p 0 * coordPartial 0 (fun q => F (saddlePolarChart q)) p) :
    (planarHessian F (saddlePolarChart p)).det < 0 := by
  rw [saddlePolarChart_hessian_det_on hF hU hp hr.ne']
  apply div_neg_of_neg_of_pos _ (sq_pos_of_ne_zero hr.ne')
  have hm := mul_neg_of_neg_of_pos hrr hangular
  nlinarith [sq_nonneg (planarHessian (fun q => F (saddlePolarChart q)) p 0 1 -
    coordPartial 1 (fun q => F (saddlePolarChart q)) p / p 0)]

theorem saddlePolarChart_gaussianCurvature_neg_on {F : Coord → ℝ} {U : Set Coord}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    {p : Coord} (hp : saddlePolarChart p ∈ U) (hr : 0 < p 0)
    (hrr : planarHessian (fun q => F (saddlePolarChart q)) p 0 0 < 0)
    (hangular : 0 < planarHessian (fun q => F (saddlePolarChart q)) p 1 1 +
      p 0 * coordPartial 0 (fun q => F (saddlePolarChart q)) p) :
    gaussianCurvature (inducedMetric (planarSupportMap F)) (saddlePolarChart p) < 0 := by
  have hd := saddlePolarChart_hessian_det_neg_on hF hU hp hr hrr hangular
  exact (planarSupportMap_negative_curvature_iff hF hU hp hd.ne).mpr hd

end
end TightVer401
