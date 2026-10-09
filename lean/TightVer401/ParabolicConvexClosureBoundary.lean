import TightVer401.RevolutionEndGeometry

/-! Actual smooth parabolic endpoint collars. The height radius has a square-root
singularity at an endpoint; the radial parameter t gives a regular smooth map. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Matrix RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false

def parabolicConvexClosureCollar (σ RN mu h : ℝ) (p : Coord) : Ambient :=
  (RN + mu * p 1) • revolutionRadial (p 0) +
    (σ * (h - mu * (p 1)^2 / 2)) • revolutionAxis

theorem parabolicConvexClosureCollar_contDiff (σ RN mu h : ℝ) :
    ContDiff ℝ ∞ (parabolicConvexClosureCollar σ RN mu h) := by
  have h0 : ContDiff ℝ ∞ (fun p : Coord => p 0) := contDiff_apply ℝ ℝ 0
  have h1 : ContDiff ℝ ∞ (fun p : Coord => p 1) := contDiff_apply ℝ ℝ 1
  exact ((contDiff_const.add (contDiff_const.mul h1)).smul
    (revolutionRadial_contDiff.comp h0)).add
    ((contDiff_const.mul (contDiff_const.sub
      ((contDiff_const.mul (h1.pow 2)).div_const 2))).smul contDiff_const)

theorem parabolicConvexClosureCollar_partial (σ RN mu h : ℝ) (p : Coord) (i : Fin 2) :
    coordPartial i (parabolicConvexClosureCollar σ RN mu h) p =
      (mu * (Pi.single i (1 : ℝ) : Coord) 1) • revolutionRadial (p 0) +
      ((RN + mu * p 1) * (Pi.single i (1 : ℝ) : Coord) 0) • revolutionAngular (p 0) -
      (σ * mu * p 1 * (Pi.single i (1 : ℝ) : Coord) 1) • revolutionAxis := by
  have hz := (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)).hasFDerivAt (x := p)
  have he := (revolutionRadial_hasDerivAt (p 0)).hasFDerivAt.comp p
    (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)).hasFDerivAt
  have hr := (hasFDerivAt_const (c := RN) p).add
    ((hasFDerivAt_const (c := mu) p).mul hz)
  have hh := (hasFDerivAt_const (c := σ) p).mul
    ((hasFDerivAt_const (c := h) p).sub
      (((hasFDerivAt_const (c := mu) p).mul (hz.pow 2)).mul_const (2 : ℝ)⁻¹))
  have hd := (hr.smul he).add (hh.smul (hasFDerivAt_const (c := revolutionAxis) p))
  change HasFDerivAt (parabolicConvexClosureCollar σ RN mu h) _ p at hd
  rw [coordPartial, hd.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    ContinuousLinearMap.proj_apply, zero_apply, smul_zero, zero_add, smul_smul,
    Function.comp_apply, pow_one, Pi.add_apply, Pi.mul_apply]
  module

theorem parabolicConvexClosureCollar_partial_theta (σ RN mu h : ℝ) (p : Coord) :
    coordPartial 0 (parabolicConvexClosureCollar σ RN mu h) p =
      (RN + mu * p 1) • revolutionAngular (p 0) := by
  simpa using parabolicConvexClosureCollar_partial σ RN mu h p 0

theorem parabolicConvexClosureCollar_partial_radial (σ RN mu h : ℝ) (p : Coord) :
    coordPartial 1 (parabolicConvexClosureCollar σ RN mu h) p =
      mu • revolutionRadial (p 0) - (σ * mu * p 1) • revolutionAxis := by
  simpa using parabolicConvexClosureCollar_partial σ RN mu h p 1

/-- In particular the differential is regular at t=0, where the height parameter fails. -/
theorem parabolicConvexClosureCollar_differential_injective {σ RN mu h : ℝ}
    (hmu : mu ≠ 0) {p : Coord} (hr : RN + mu * p 1 ≠ 0) :
    Function.Injective (fderiv ℝ (parabolicConvexClosureCollar σ RN mu h) p) := by
  rcases revolution_frame (p 0) with ⟨hrr, haa, _, hra, hrz, haz⟩
  have har : inner ℝ (revolutionAngular (p 0)) (revolutionRadial (p 0)) = 0 := by
    rw [real_inner_comm, hra]
  have hzr : inner ℝ revolutionAxis (revolutionRadial (p 0)) = 0 := by
    rw [real_inner_comm, hrz]
  have hza : inner ℝ revolutionAxis (revolutionAngular (p 0)) = 0 := by
    rw [real_inner_comm, haz]
  intro v w hvw
  have he : fderiv ℝ (parabolicConvexClosureCollar σ RN mu h) p (v - w) = 0 := by
    simp [map_sub, hvw]
  have h1 : (v - w) 1 = 0 := by
    have e := congrArg (fun x : Ambient => inner ℝ x (revolutionRadial (p 0))) he
    simp only [fderiv_two_coordinates, parabolicConvexClosureCollar_partial_theta,
      parabolicConvexClosureCollar_partial_radial, inner_add_left, inner_sub_left,
      real_inner_smul_left, inner_zero_left, har, hrr, hzr,
      mul_zero, sub_zero, zero_add, mul_one] at e
    exact (mul_eq_zero.mp e).resolve_right hmu
  have h0 : (v - w) 0 = 0 := by
    have e := congrArg (fun x : Ambient => inner ℝ x (revolutionAngular (p 0))) he
    simp only [fderiv_two_coordinates, parabolicConvexClosureCollar_partial_theta,
      parabolicConvexClosureCollar_partial_radial, inner_add_left, inner_sub_left,
      real_inner_smul_left, inner_zero_left, hra, haa, hza,
      mul_zero, sub_zero, add_zero, mul_one] at e
    exact (mul_eq_zero.mp e).resolve_right hr
  apply sub_eq_zero.mp
  ext i
  fin_cases i <;> assumption

theorem parabolicConvexClosureCollar_upper_eq {RN mu h δ : ℝ} {r : ℝ → ℝ}
    (hmu : 0 < mu)
    (hg : EqOn r (fun z => RN + Real.sqrt (2 * mu * (h - z))) (Icc (h - δ) h))
    {θ t : ℝ} (ht : 0 ≤ t) (hsmall : mu * t^2 / 2 ≤ δ) :
    parabolicConvexClosureCollar 1 RN mu h (![θ, t] : Coord) =
      revolutionEnd r (![θ, h - mu * t^2 / 2] : Coord) := by
  have hz : h - mu * t^2 / 2 ∈ Icc (h - δ) h := ⟨by linarith, by nlinarith⟩
  have hs : Real.sqrt (2 * mu * (h - (h - mu * t^2 / 2))) = mu * t := by
    rw [show 2 * mu * (h - (h - mu * t^2 / 2)) = (mu * t)^2 by ring,
      Real.sqrt_sq_eq_abs, abs_of_nonneg (mul_nonneg hmu.le ht)]
  have hrad : r (h - mu * t^2 / 2) = RN + mu * t :=
    (hg hz).trans (congrArg (fun x : ℝ => RN + x) hs)
  simp [parabolicConvexClosureCollar, revolutionEnd, hrad]

theorem parabolicConvexClosureCollar_lower_eq {RN mu h δ : ℝ} {r : ℝ → ℝ}
    (hmu : 0 < mu)
    (hg : EqOn r (fun z => RN + Real.sqrt (2 * mu * (h + z))) (Icc (-h) (-h + δ)))
    {θ t : ℝ} (ht : 0 ≤ t) (hsmall : mu * t^2 / 2 ≤ δ) :
    parabolicConvexClosureCollar (-1) RN mu h (![θ, t] : Coord) =
      revolutionEnd r (![θ, -h + mu * t^2 / 2] : Coord) := by
  have hz : -h + mu * t^2 / 2 ∈ Icc (-h) (-h + δ) := ⟨by nlinarith, by linarith⟩
  have hs : Real.sqrt (2 * mu * (h + (-h + mu * t^2 / 2))) = mu * t := by
    rw [show 2 * mu * (h + (-h + mu * t^2 / 2)) = (mu * t)^2 by ring,
      Real.sqrt_sq_eq_abs, abs_of_nonneg (mul_nonneg hmu.le ht)]
  have hrad : r (-h + mu * t^2 / 2) = RN + mu * t :=
    (hg hz).trans (congrArg (fun x : ℝ => RN + x) hs)
  simp [parabolicConvexClosureCollar, revolutionEnd, hrad]
  module

end
end TightVer401
