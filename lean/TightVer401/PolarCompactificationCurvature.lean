import TightVer401.PolarCompactificationGeometry
import TightVer401.RevolutionEndSecondForm

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Matrix
set_option backward.isDefEq.respectTransparency false

def polarCompactificationNormal (p : Coord) : Ambient :=
  Real.sin (p 1) • revolutionRadial (p 0) + Real.cos (p 1) • revolutionAxis

theorem polarCompactification_isUnitNormal (R a C : ℝ) (p : Coord) :
    IsUnitNormalAt (polarCompactification R a C) (polarCompactificationNormal p) p := by
  rcases revolution_frame (p 0) with ⟨hrr, haa, hzz, hra, hrz, haz⟩
  have har : inner ℝ (revolutionAngular (p 0)) (revolutionRadial (p 0)) = 0 := by rw [real_inner_comm, hra]
  have hzr : inner ℝ revolutionAxis (revolutionRadial (p 0)) = 0 := by rw [real_inner_comm, hrz]
  constructor
  · simp only [polarCompactificationNormal, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right, hrr, hzz, hrz, hzr,
      mul_zero, zero_mul, add_zero, zero_add, mul_one]
    nlinarith [Real.sin_sq_add_cos_sq (p 1)]
  · have horth (i : Fin 2) : inner ℝ (coordPartial i (polarCompactification R a C) p)
        (polarCompactificationNormal p) = 0 := by
      fin_cases i
      · change inner ℝ (coordPartial 0 (polarCompactification R a C) p)
          (polarCompactificationNormal p) = 0
        rw [polarCompactification_partial_theta]
        simp [polarCompactificationNormal, inner_add_right, real_inner_smul_left,
          real_inner_smul_right, har, haz]
      · change inner ℝ (coordPartial 1 (polarCompactification R a C) p)
          (polarCompactificationNormal p) = 0
        rw [polarCompactification_partial_transverse]
        simp only [polarCompactificationNormal, inner_add_left, inner_add_right,
          real_inner_smul_left, real_inner_smul_right, hrr, hzz, hrz, hzr,
          mul_zero, zero_mul, add_zero, zero_add, mul_one]
        ring
    intro v
    rw [fderiv_two_coordinates, inner_add_left, real_inner_smul_left,
      real_inner_smul_left, horth 0, horth 1]
    simp

theorem polarCompactification_second_theta (R a C : ℝ) (p : Coord) :
    coordPartial 0 (coordPartial 0 (polarCompactification R a C)) p =
      (R - a * Real.sin (p 1)) • revolutionRadial (p 0) := by
  rw [show coordPartial 0 (polarCompactification R a C) =
    (fun z => (a * Real.sin (z 1) - R) • revolutionAngular (z 0)) from
      funext (polarCompactification_partial_theta R a C)]
  rw [revolution_curve_product_partial (((Real.hasDerivAt_sin (p 1)).const_mul a).sub_const R)
    (revolutionAngular_hasDerivAt (p 0))]
  simp
  module

theorem polarCompactification_second_mixed (R a C : ℝ) (p : Coord) :
    coordPartial 1 (coordPartial 0 (polarCompactification R a C)) p =
      (a * Real.cos (p 1)) • revolutionAngular (p 0) := by
  rw [show coordPartial 0 (polarCompactification R a C) =
    (fun z => (a * Real.sin (z 1) - R) • revolutionAngular (z 0)) from
      funext (polarCompactification_partial_theta R a C)]
  rw [revolution_curve_product_partial (((Real.hasDerivAt_sin (p 1)).const_mul a).sub_const R)
    (revolutionAngular_hasDerivAt (p 0))]
  simp

theorem polarCompactification_second_transverse (R a C : ℝ) (p : Coord) :
    coordPartial 1 (coordPartial 1 (polarCompactification R a C)) p =
      (-a * Real.sin (p 1)) • revolutionRadial (p 0) +
        (-a * Real.cos (p 1)) • revolutionAxis := by
  let f : Coord → Ambient := fun z => (a * Real.cos (z 1)) • revolutionRadial (z 0)
  let g : Coord → Ambient := fun z => (-a * Real.sin (z 1)) • revolutionAxis
  have hf : ContDiff ℝ ∞ f :=
    (contDiff_const.mul (Real.contDiff_cos.comp (contDiff_apply ℝ ℝ 1))).smul
      (revolutionRadial_contDiff.comp (contDiff_apply ℝ ℝ 0))
  have hg : ContDiff ℝ ∞ g :=
    (contDiff_const.mul (Real.contDiff_sin.comp (contDiff_apply ℝ ℝ 1))).smul contDiff_const
  rw [show coordPartial 1 (polarCompactification R a C) = (fun z => f z + g z) from
    funext (polarCompactification_partial_transverse R a C)]
  simp only [coordPartial, fderiv_fun_add (hf.differentiable (by simp) p)
    (hg.differentiable (by simp) p), add_apply]
  change coordPartial 1 f p + coordPartial 1 g p = _
  dsimp [f, g]
  rw [revolution_curve_product_partial ((Real.hasDerivAt_cos (p 1)).const_mul a)
    (revolutionRadial_hasDerivAt (p 0)),
    revolution_curve_product_partial ((Real.hasDerivAt_sin (p 1)).const_mul (-a))
      (hasDerivAt_const (p 0) revolutionAxis)]
  simp

theorem polarCompactification_secondFundamental (R a C : ℝ) (p : Coord) :
    secondFundamental (polarCompactification R a C) (polarCompactificationNormal p) p =
      ![![(R - a * Real.sin (p 1)) * Real.sin (p 1), 0], ![0, -a]] := by
  rcases revolution_frame (p 0) with ⟨hrr, _, hzz, hra, hrz, haz⟩
  have har : inner ℝ (revolutionAngular (p 0)) (revolutionRadial (p 0)) = 0 := by rw [real_inner_comm, hra]
  have hzr : inner ℝ revolutionAxis (revolutionRadial (p 0)) = 0 := by rw [real_inner_comm, hrz]
  have hcomm := coordPartial_comm (polarCompactification_contDiff R a C).contDiffOn
    isOpen_univ (mem_univ p) 0 1
  ext i j
  fin_cases i <;> fin_cases j
  · change inner ℝ (coordPartial 0 (coordPartial 0 (polarCompactification R a C)) p)
      (polarCompactificationNormal p) = (R - a * Real.sin (p 1)) * Real.sin (p 1)
    rw [polarCompactification_second_theta]
    simp only [polarCompactificationNormal, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, hrr, hrz, mul_one, mul_zero, add_zero]
    ring
  · change inner ℝ (coordPartial 0 (coordPartial 1 (polarCompactification R a C)) p)
      (polarCompactificationNormal p) = 0
    rw [hcomm, polarCompactification_second_mixed]
    simp [polarCompactificationNormal, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, har, haz]
  · change inner ℝ (coordPartial 1 (coordPartial 0 (polarCompactification R a C)) p)
      (polarCompactificationNormal p) = 0
    rw [polarCompactification_second_mixed]
    simp [polarCompactificationNormal, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, har, haz]
  · change inner ℝ (coordPartial 1 (coordPartial 1 (polarCompactification R a C)) p)
      (polarCompactificationNormal p) = -a
    rw [polarCompactification_second_transverse]
    simp only [polarCompactificationNormal, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right, hrr, hzz, hrz, hzr,
      mul_zero, zero_mul, add_zero, zero_add, mul_one]
    have ht := congrArg (fun x : ℝ => a * x) (Real.sin_sq_add_cos_sq (p 1))
    nlinarith [ht]

theorem polarCompactification_gaussianCurvature {R a C : ℝ}
    (ha : 0 < a) (hR : a < R) (p : Coord) :
    gaussianCurvature (inducedMetric (polarCompactification R a C)) p =
      Real.sin (p 1) / (a * (a * Real.sin (p 1) - R)) := by
  have hX := (polarCompactification_contDiff R a C).contDiffOn (s := univ)
  have hg := inducedMetric_smoothPositiveOn hX isOpen_univ
    (fun z _ => polarCompactification_differential_injective ha hR z)
  rw [curvature_eq_second_form_det_div_metric_det hg (inducedMetric_isometricOn hX)
    isOpen_univ (mem_univ p) (polarCompactification_isUnitNormal R a C p),
    polarCompactification_secondFundamental, polarCompactification_metric, Matrix.det_fin_two,
    Matrix.det_fin_two]
  have hb : a * Real.sin (p 1) - R ≠ 0 := by
    have hh := mul_le_mul_of_nonneg_left (Real.sin_le_one (p 1)) ha.le
    linarith
  simp
  field_simp [ha.ne', hb] <;> ring

theorem polarCompactification_gaussianCurvature_neg {R a C : ℝ}
    (ha : 0 < a) (hR : a < R) {p : Coord} (hs : 0 < Real.sin (p 1)) :
    gaussianCurvature (inducedMetric (polarCompactification R a C)) p < 0 := by
  rw [polarCompactification_gaussianCurvature ha hR]
  have hb : a * Real.sin (p 1) - R < 0 := by
    have hh := mul_le_mul_of_nonneg_left (Real.sin_le_one (p 1)) ha.le
    linarith
  exact div_neg_of_pos_of_neg hs (mul_neg_of_pos_of_neg ha hb)

end
end TightVer401
