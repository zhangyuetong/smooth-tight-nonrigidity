import TightVer401.DualRadialQuadraticGerm
import TightVer401.PolarCompactificationGeometry

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Matrix
set_option backward.isDefEq.respectTransparency false

/-- The puncture resolves into an angular boundary circle; the transverse
parameter is allowed to be zero and the actual surface stays regular there. -/
def dualRadialQuadraticCompactification (R M d : ℝ) (p : Coord) : Ambient :=
  (M * R - M * p 1) • revolutionRadial (p 0) +
    (d + M / 2 * (p 1) ^ 2) • revolutionAxis

def dualRadialQuadraticSource (θ r : ℝ) : Coord :=
  ![r * Real.cos θ, r * Real.sin θ]

theorem dualRadialQuadraticSource_sq (θ r : ℝ) :
    (dualRadialQuadraticSource θ r) 0 ^ 2 +
      (dualRadialQuadraticSource θ r) 1 ^ 2 = r ^ 2 := by
  dsimp [dualRadialQuadraticSource]
  nlinarith [congrArg (fun x : ℝ => r ^ 2 * x) (Real.sin_sq_add_cos_sq θ)]

theorem dualRadialQuadraticSource_radius {θ r : ℝ} (hr : 0 < r) :
    planarRadius (dualRadialQuadraticSource θ r) = r := by
  rw [planarRadius, dualRadialQuadraticSource_sq, Real.sqrt_sq hr.le]

theorem dualRadialQuadraticCompactification_eq_support (R M d : ℝ)
    {θ r : ℝ} (hr : 0 < r) :
    dualRadialQuadraticCompactification R M d ![θ, r] =
      planarSupportMap (dualRadialQuadraticPotential R M d) (dualRadialQuadraticSource θ r) := by
  have hp : 0 < (dualRadialQuadraticSource θ r) 0 ^ 2 +
      (dualRadialQuadraticSource θ r) 1 ^ 2 := by
    rw [dualRadialQuadraticSource_sq]
    exact sq_pos_of_pos hr
  rw [dualRadialQuadraticPotential_supportMap hp, dualRadialQuadraticSource_radius hr]
  ext i
  fin_cases i <;> simp [dualRadialQuadraticCompactification,
    dualRadialQuadraticSource, revolutionRadial, revolutionAxis]
  all_goals field_simp [hr.ne'] <;> ring

theorem dualRadialQuadraticCompactification_contDiff (R M d : ℝ) :
    ContDiff ℝ ∞ (dualRadialQuadraticCompactification R M d) := by
  have h₀ : ContDiff ℝ ∞ (fun p : Coord => p 0) := contDiff_apply ℝ ℝ 0
  have h₁ : ContDiff ℝ ∞ (fun p : Coord => p 1) := contDiff_apply ℝ ℝ 1
  exact ((contDiff_const.sub (contDiff_const.mul h₁)).smul
    (revolutionRadial_contDiff.comp h₀)).add
    ((contDiff_const.add (contDiff_const.mul (h₁.pow 2))).smul contDiff_const)

theorem dualRadialQuadraticCompactification_partial (R M d : ℝ) (p : Coord) (i : Fin 2) :
    coordPartial i (dualRadialQuadraticCompactification R M d) p =
      (-M * (Pi.single i (1 : ℝ) : Coord) 1) • revolutionRadial (p 0) +
      ((M * R - M * p 1) * (Pi.single i (1 : ℝ) : Coord) 0) • revolutionAngular (p 0) +
      (M * p 1 * (Pi.single i (1 : ℝ) : Coord) 1) • revolutionAxis := by
  have hs := ((hasDerivAt_const (p 1) (M * R)).sub
    ((hasDerivAt_id (p 1)).const_mul M)).hasFDerivAt.comp p
    (ContinuousLinearMap.proj (R := ℝ) 1).hasFDerivAt
  have hc := ((((hasDerivAt_id (p 1)).pow 2).const_mul (M / 2)).const_add d).hasFDerivAt.comp p
    (ContinuousLinearMap.proj (R := ℝ) 1).hasFDerivAt
  have he := (revolutionRadial_hasDerivAt (p 0)).hasFDerivAt.comp p
    (ContinuousLinearMap.proj (R := ℝ) 0).hasFDerivAt
  have hd := (hs.smul he).add (hc.smul (hasFDerivAt_const (c := revolutionAxis) p))
  change HasFDerivAt (dualRadialQuadraticCompactification R M d) _ p at hd
  rw [coordPartial, hd.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.proj_apply,
    zero_apply, smul_zero, zero_add, smul_smul, Function.comp_apply,
    Pi.sub_apply, Pi.pow_apply, id_eq]
  norm_num
  module

theorem dualRadialQuadraticCompactification_partial_theta (R M d : ℝ) (p : Coord) :
    coordPartial 0 (dualRadialQuadraticCompactification R M d) p =
      (M * R - M * p 1) • revolutionAngular (p 0) := by
  simpa using dualRadialQuadraticCompactification_partial R M d p 0

theorem dualRadialQuadraticCompactification_partial_transverse (R M d : ℝ) (p : Coord) :
    coordPartial 1 (dualRadialQuadraticCompactification R M d) p =
      (-M) • revolutionRadial (p 0) + (M * p 1) • revolutionAxis := by
  simpa using dualRadialQuadraticCompactification_partial R M d p 1

theorem dualRadialQuadraticCompactification_boundary (R M d θ : ℝ) :
    dualRadialQuadraticCompactification R M d ![θ, 0] =
      (M * R) • revolutionRadial θ + d • revolutionAxis := by
  simp [dualRadialQuadraticCompactification]

theorem dualRadialQuadraticCompactification_boundary_partials (R M d θ : ℝ) :
    coordPartial 0 (dualRadialQuadraticCompactification R M d) ![θ, 0] =
      (M * R) • revolutionAngular θ ∧
    coordPartial 1 (dualRadialQuadraticCompactification R M d) ![θ, 0] =
      (-M) • revolutionRadial θ := by
  constructor
  · simp [dualRadialQuadraticCompactification_partial_theta]
  · simp [dualRadialQuadraticCompactification_partial_transverse]

theorem dualRadialQuadraticCompactification_metric (R M d : ℝ) (p : Coord) :
    inducedMetric (dualRadialQuadraticCompactification R M d) p =
      ![![(M * R - M * p 1)^2, 0], ![0, M^2 * (1 + (p 1)^2)]] := by
  rcases revolution_frame (p 0) with ⟨hrr, haa, hzz, hra, hrz, haz⟩
  have har : inner ℝ (revolutionAngular (p 0)) (revolutionRadial (p 0)) = 0 := by
    rw [real_inner_comm, hra]
  have hzr : inner ℝ revolutionAxis (revolutionRadial (p 0)) = 0 := by
    rw [real_inner_comm, hrz]
  have hza : inner ℝ revolutionAxis (revolutionAngular (p 0)) = 0 := by
    rw [real_inner_comm, haz]
  ext i j
  fin_cases i <;> fin_cases j
  · change inner ℝ (coordPartial 0 (dualRadialQuadraticCompactification R M d) p)
      (coordPartial 0 (dualRadialQuadraticCompactification R M d) p) = (M * R - M * p 1)^2
    rw [dualRadialQuadraticCompactification_partial_theta]
    simp only [real_inner_smul_left, real_inner_smul_right, haa, mul_one]
    ring
  · change inner ℝ (coordPartial 0 (dualRadialQuadraticCompactification R M d) p)
      (coordPartial 1 (dualRadialQuadraticCompactification R M d) p) = 0
    rw [dualRadialQuadraticCompactification_partial_theta,
      dualRadialQuadraticCompactification_partial_transverse]
    simp [inner_add_right, real_inner_smul_left, real_inner_smul_right, har, haz]
  · change inner ℝ (coordPartial 1 (dualRadialQuadraticCompactification R M d) p)
      (coordPartial 0 (dualRadialQuadraticCompactification R M d) p) = 0
    rw [dualRadialQuadraticCompactification_partial_theta,
      dualRadialQuadraticCompactification_partial_transverse]
    simp [inner_add_left, real_inner_smul_left, real_inner_smul_right, hra, hza]
  · change inner ℝ (coordPartial 1 (dualRadialQuadraticCompactification R M d) p)
      (coordPartial 1 (dualRadialQuadraticCompactification R M d) p) = M^2 * (1 + (p 1)^2)
    rw [dualRadialQuadraticCompactification_partial_transverse]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      hrr, hzz, hrz, hzr, mul_zero, zero_mul, add_zero, zero_add, mul_one]
    ring

theorem dualRadialQuadraticCompactification_differential_injective {R M d : ℝ}
    (hM : 0 < M) (p : Coord) (hr : p 1 < R) :
    Function.Injective (fderiv ℝ (dualRadialQuadraticCompactification R M d) p) := by
  have hfactor : 0 < M * R - M * p 1 := by nlinarith [mul_pos hM (sub_pos.mpr hr)]
  intro v w hvw
  have hz : fderiv ℝ (dualRadialQuadraticCompactification R M d) p (v - w) = 0 := by
    simp [map_sub, hvw]
  have hn := congrArg (fun x : Ambient => inner ℝ x x) hz
  rw [inducedMetric_bilinear, dualRadialQuadraticCompactification_metric] at hn
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, mul_zero, zero_mul, add_zero, zero_add,
    inner_zero_left] at hn
  have ht : 0 < (M * R - M * p 1)^2 := sq_pos_of_pos hfactor
  have hm : 0 < M^2 * (1 + (p 1)^2) := mul_pos (sq_pos_of_pos hM) (by positivity)
  have h₀ : (v - w) 0 = 0 := by
    have h₁ : 0 ≤ (M^2 * (1 + (p 1)^2)) * ((v - w) 1)^2 :=
      mul_nonneg hm.le (sq_nonneg _)
    have h₂ : (M * R - M * p 1)^2 * ((v - w) 0)^2 = 0 := by
      nlinarith [sq_nonneg ((v-w) 0)]
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp h₂).resolve_left ht.ne')
  have h₁ : (v - w) 1 = 0 := by
    have h₂ : (M^2 * (1 + (p 1)^2)) * ((v - w) 1)^2 = 0 := by
      rw [h₀] at hn
      nlinarith
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp h₂).resolve_left hm.ne')
  apply sub_eq_zero.mp
  ext i
  fin_cases i <;> assumption

theorem dualRadialQuadraticCompactification_boundary_regular {R M d : ℝ}
    (hR : 0 < R) (hM : 0 < M) (θ : ℝ) :
    Function.Injective (fderiv ℝ (dualRadialQuadraticCompactification R M d) ![θ, 0]) := by
  exact dualRadialQuadraticCompactification_differential_injective hM _ (by simpa)

/-- The precise northern parabolic collar, with paper radius R_N=M R. -/
def dualRadialQuadraticNorthernCollar (R M h : ℝ) (p : Coord) : Ambient :=
  (M * R + M * p 1) • revolutionRadial (p 0) +
    (h - M / 2 * (p 1)^2) • revolutionAxis

theorem dualRadialQuadraticNorthernCollar_eq_compactification (R M h : ℝ) (p : Coord) :
    dualRadialQuadraticNorthernCollar R M h p =
      -dualRadialQuadraticCompactification R M (-h) ![p 0 + Real.pi, -p 1] := by
  ext i
  fin_cases i <;> simp [dualRadialQuadraticNorthernCollar,
    dualRadialQuadraticCompactification, revolutionRadial, revolutionAxis,
    Real.cos_add_pi, Real.sin_add_pi] <;> ring

end
end TightVer401
