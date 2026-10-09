import TightVer401.RevolutionEndCalculus

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Matrix RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false

def revolutionWeight (s : ℝ) : ℝ := Real.sqrt (1 + s ^ 2)
def revolutionEndNormal (q : ℝ → ℝ) (p : Coord) : Ambient :=
  (-1 / revolutionWeight (deriv q (p 1))) • revolutionRadial (p 0) +
    (deriv q (p 1) / revolutionWeight (deriv q (p 1))) • revolutionAxis

theorem revolutionWeight_pos (s : ℝ) : 0 < revolutionWeight s := by
  apply Real.sqrt_pos.mpr
  positivity

theorem revolutionWeight_sq (s : ℝ) : revolutionWeight s ^ 2 = 1 + s ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem revolutionEnd_metric {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q) (p : Coord) :
    inducedMetric (revolutionEnd q) p = ![![q (p 1)^2, 0], ![0, 1 + deriv q (p 1)^2]] := by
  have hd := (hq.differentiable (by simp) (p 1)).hasDerivAt
  rcases revolution_frame (p 0) with ⟨hrr, haa, hzz, hra, hrz, haz⟩
  have har : inner ℝ (revolutionAngular (p 0)) (revolutionRadial (p 0)) = 0 := by rw [real_inner_comm, hra]
  have hzr : inner ℝ revolutionAxis (revolutionRadial (p 0)) = 0 := by rw [real_inner_comm, hrz]
  have hza : inner ℝ revolutionAxis (revolutionAngular (p 0)) = 0 := by rw [real_inner_comm, haz]
  ext i j
  fin_cases i <;> fin_cases j
  · change inner ℝ (coordPartial 0 (revolutionEnd q) p) (coordPartial 0 (revolutionEnd q) p) = q (p 1)^2
    rw [revolutionEnd_partial_theta hd]
    simp only [real_inner_smul_left, real_inner_smul_right, haa, mul_one]
    ring
  · change inner ℝ (coordPartial 0 (revolutionEnd q) p) (coordPartial 1 (revolutionEnd q) p) = 0
    rw [revolutionEnd_partial_theta hd, revolutionEnd_partial_height hd]
    simp only [inner_add_right, real_inner_smul_left, real_inner_smul_right, har, haz, mul_zero, add_zero]
  · change inner ℝ (coordPartial 1 (revolutionEnd q) p) (coordPartial 0 (revolutionEnd q) p) = 0
    rw [revolutionEnd_partial_theta hd, revolutionEnd_partial_height hd]
    simp only [inner_add_left, real_inner_smul_left, real_inner_smul_right, hra, hza, mul_zero, add_zero]
  · change inner ℝ (coordPartial 1 (revolutionEnd q) p) (coordPartial 1 (revolutionEnd q) p) = 1 + deriv q (p 1)^2
    rw [revolutionEnd_partial_height hd]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, hrr, hzz, hrz, hzr, mul_zero, zero_mul, add_zero, zero_add, mul_one]
    ring

theorem revolutionEndNormal_unit (q : ℝ → ℝ) (p : Coord) :
    inner ℝ (revolutionEndNormal q p) (revolutionEndNormal q p) = 1 := by
  rcases revolution_frame (p 0) with ⟨hrr, _, hzz, _, hrz, _⟩
  have hzr : inner ℝ revolutionAxis (revolutionRadial (p 0)) = 0 := by rw [real_inner_comm, hrz]
  have hw := ne_of_gt (revolutionWeight_pos (deriv q (p 1)))
  simp only [revolutionEndNormal, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, hrr, hzz, hrz, hzr]
  field_simp [hw]
  nlinarith [revolutionWeight_sq (deriv q (p 1))]

theorem revolutionEnd_isUnitNormal {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q) (p : Coord) :
    IsUnitNormalAt (revolutionEnd q) (revolutionEndNormal q p) p := by
  refine ⟨revolutionEndNormal_unit q p, ?_⟩
  have hd := (hq.differentiable (by simp) (p 1)).hasDerivAt
  rcases revolution_frame (p 0) with ⟨hrr, _, hzz, hra, hrz, haz⟩
  have har : inner ℝ (revolutionAngular (p 0)) (revolutionRadial (p 0)) = 0 := by rw [real_inner_comm, hra]
  have hzr : inner ℝ revolutionAxis (revolutionRadial (p 0)) = 0 := by rw [real_inner_comm, hrz]
  have horth (i : Fin 2) : inner ℝ (coordPartial i (revolutionEnd q) p) (revolutionEndNormal q p) = 0 := by
    fin_cases i
    · change inner ℝ (coordPartial 0 (revolutionEnd q) p) (revolutionEndNormal q p) = 0
      rw [revolutionEnd_partial_theta hd]
      simp only [revolutionEndNormal, inner_add_right, real_inner_smul_left, real_inner_smul_right, har, haz]
      ring
    · change inner ℝ (coordPartial 1 (revolutionEnd q) p) (revolutionEndNormal q p) = 0
      rw [revolutionEnd_partial_height hd]
      simp only [revolutionEndNormal, inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, hrr, hzz, hrz, hzr]
      ring
  intro v
  rw [fderiv_two_coordinates, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    horth 0, horth 1]
  simp

theorem revolutionEnd_differential_injective {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    {p : Coord} (hqp : q (p 1) ≠ 0) : Function.Injective (fderiv ℝ (revolutionEnd q) p) := by
  have hd := (hq.differentiable (by simp) (p 1)).hasDerivAt
  rcases revolution_frame (p 0) with ⟨_, haa, hzz, hra, hrz, haz⟩
  have hza : inner ℝ revolutionAxis (revolutionAngular (p 0)) = 0 := by rw [real_inner_comm, haz]
  intro v w hvw
  have hz : fderiv ℝ (revolutionEnd q) p (v - w) = 0 := by simp [map_sub, hvw]
  have h1 : (v - w) 1 = 0 := by
    have h := congrArg (fun x : Ambient => inner ℝ x revolutionAxis) hz
    simp only [fderiv_two_coordinates, revolutionEnd_partial_theta hd, revolutionEnd_partial_height hd,
      inner_add_left, real_inner_smul_left, inner_zero_left, haz, hrz, hzz,
      mul_zero, zero_add, mul_one, add_zero] at h
    exact h
  have h0 : (v - w) 0 = 0 := by
    have h := congrArg (fun x : Ambient => inner ℝ x (revolutionAngular (p 0))) hz
    simp only [fderiv_two_coordinates, revolutionEnd_partial_theta hd, revolutionEnd_partial_height hd,
      inner_add_left, real_inner_smul_left, inner_zero_left, h1, zero_mul, zero_add,
      haa, hra, hza, mul_one, add_zero, mul_zero] at h
    exact (mul_eq_zero.mp h).resolve_right hqp
  apply sub_eq_zero.mp
  ext i
  fin_cases i <;> assumption

end
end TightVer401
