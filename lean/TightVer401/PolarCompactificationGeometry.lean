import TightVer401.PolarCompactificationCalculus

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Matrix
set_option backward.isDefEq.respectTransparency false

theorem polarCompactification_metric (R a C : ℝ) (p : Coord) :
    inducedMetric (polarCompactification R a C) p =
      ![![(a * Real.sin (p 1) - R)^2, 0], ![0, a^2]] := by
  rcases revolution_frame (p 0) with ⟨hrr, haa, hzz, hra, hrz, haz⟩
  have har : inner ℝ (revolutionAngular (p 0)) (revolutionRadial (p 0)) = 0 := by
    rw [real_inner_comm, hra]
  have hzr : inner ℝ revolutionAxis (revolutionRadial (p 0)) = 0 := by
    rw [real_inner_comm, hrz]
  have hza : inner ℝ revolutionAxis (revolutionAngular (p 0)) = 0 := by
    rw [real_inner_comm, haz]
  ext i j
  fin_cases i <;> fin_cases j
  · change inner ℝ (coordPartial 0 (polarCompactification R a C) p)
      (coordPartial 0 (polarCompactification R a C) p) = (a * Real.sin (p 1) - R)^2
    rw [polarCompactification_partial_theta]
    simp only [real_inner_smul_left, real_inner_smul_right, haa, mul_one]
    ring
  · change inner ℝ (coordPartial 0 (polarCompactification R a C) p)
      (coordPartial 1 (polarCompactification R a C) p) = 0
    rw [polarCompactification_partial_theta, polarCompactification_partial_transverse]
    simp only [inner_add_right, real_inner_smul_left, real_inner_smul_right,
      har, haz, mul_zero, add_zero]
  · change inner ℝ (coordPartial 1 (polarCompactification R a C) p)
      (coordPartial 0 (polarCompactification R a C) p) = 0
    rw [polarCompactification_partial_theta, polarCompactification_partial_transverse]
    simp only [inner_add_left, real_inner_smul_left, real_inner_smul_right,
      hra, hza, mul_zero, add_zero]
  · change inner ℝ (coordPartial 1 (polarCompactification R a C) p)
      (coordPartial 1 (polarCompactification R a C) p) = a^2
    rw [polarCompactification_partial_transverse]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      hrr, hzz, hrz, hzr, mul_zero, zero_mul, add_zero, zero_add, mul_one]
    have htrig := congrArg (fun x : ℝ => a^2 * x) (Real.sin_sq_add_cos_sq (p 1))
    nlinarith [htrig]

theorem polarCompactification_boundary_metric (R a C θ : ℝ) :
    inducedMetric (polarCompactification R a C) ![θ, 0] =
      ![![R^2, 0], ![0, a^2]] := by
  simp [polarCompactification_metric]

theorem polarCompactification_differential_injective {R a C : ℝ}
    (ha : 0 < a) (hR : a < R) (p : Coord) :
    Function.Injective (fderiv ℝ (polarCompactification R a C) p) := by
  have hfactor : a * Real.sin (p 1) - R < 0 := by
    have hh := mul_le_mul_of_nonneg_left (Real.sin_le_one (p 1)) ha.le
    linarith
  intro v w hvw
  have hz : fderiv ℝ (polarCompactification R a C) p (v - w) = 0 := by
    simp [map_sub, hvw]
  have hn := congrArg (fun x : Ambient => inner ℝ x x) hz
  rw [inducedMetric_bilinear, polarCompactification_metric] at hn
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, mul_zero, zero_mul, add_zero, zero_add,
    inner_zero_left] at hn
  have ht : 0 < (a * Real.sin (p 1) - R)^2 := sq_pos_of_ne_zero hfactor.ne
  have ha₂ : 0 < a^2 := sq_pos_of_pos ha
  have h₀ : (v - w) 0 = 0 := by
    have h₁ : 0 ≤ a^2 * ((v - w) 1)^2 := mul_nonneg ha₂.le (sq_nonneg _)
    have h₂ : (a * Real.sin (p 1) - R)^2 * ((v - w) 0)^2 = 0 := by nlinarith [sq_nonneg ((v-w) 0)]
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp h₂).resolve_left ht.ne')
  have h₁ : (v - w) 1 = 0 := by
    have h₂ : a^2 * ((v - w) 1)^2 = 0 := by rw [h₀] at hn; nlinarith
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp h₂).resolve_left ha₂.ne')
  apply sub_eq_zero.mp
  ext i
  fin_cases i <;> assumption

end
end TightVer401
