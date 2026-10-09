import TightVer401.RevolutionEndCalculus

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Matrix
set_option backward.isDefEq.respectTransparency false

def polarCompactification (R a C : ℝ) (p : Coord) : Ambient :=
  (a * Real.sin (p 1) - R) • revolutionRadial (p 0) +
    (C + a * Real.cos (p 1)) • revolutionAxis

theorem polarCompactification_contDiff (R a C : ℝ) :
    ContDiff ℝ ∞ (polarCompactification R a C) := by
  have h₀ : ContDiff ℝ ∞ (fun p : Coord => p 0) := contDiff_apply ℝ ℝ 0
  have h₁ : ContDiff ℝ ∞ (fun p : Coord => p 1) := contDiff_apply ℝ ℝ 1
  exact (((contDiff_const.mul (Real.contDiff_sin.comp h₁)).sub contDiff_const).smul
    (revolutionRadial_contDiff.comp h₀)).add
    ((contDiff_const.add (contDiff_const.mul (Real.contDiff_cos.comp h₁))).smul contDiff_const)

theorem polarCompactification_partial (R a C : ℝ) (p : Coord) (i : Fin 2) :
    coordPartial i (polarCompactification R a C) p =
      (a * Real.cos (p 1) * (Pi.single i (1 : ℝ) : Coord) 1) • revolutionRadial (p 0) +
      ((a * Real.sin (p 1) - R) * (Pi.single i (1 : ℝ) : Coord) 0) • revolutionAngular (p 0) +
      (-a * Real.sin (p 1) * (Pi.single i (1 : ℝ) : Coord) 1) • revolutionAxis := by
  have hs := (((Real.hasDerivAt_sin (p 1)).const_mul a).sub_const R).hasFDerivAt.comp p
    (ContinuousLinearMap.proj (R := ℝ) 1).hasFDerivAt
  have hc := (((Real.hasDerivAt_cos (p 1)).const_mul a).const_add C).hasFDerivAt.comp p
    (ContinuousLinearMap.proj (R := ℝ) 1).hasFDerivAt
  have he := (revolutionRadial_hasDerivAt (p 0)).hasFDerivAt.comp p
    (ContinuousLinearMap.proj (R := ℝ) 0).hasFDerivAt
  have hd := (hs.smul he).add (hc.smul (hasFDerivAt_const (c := revolutionAxis) p))
  change HasFDerivAt (polarCompactification R a C) _ p at hd
  rw [coordPartial, hd.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.proj_apply,
    zero_apply, smul_zero, zero_add, smul_smul, Function.comp_apply]
  module

theorem polarCompactification_partial_theta (R a C : ℝ) (p : Coord) :
    coordPartial 0 (polarCompactification R a C) p =
      (a * Real.sin (p 1) - R) • revolutionAngular (p 0) := by
  simpa using polarCompactification_partial R a C p 0

theorem polarCompactification_partial_transverse (R a C : ℝ) (p : Coord) :
    coordPartial 1 (polarCompactification R a C) p =
      (a * Real.cos (p 1)) • revolutionRadial (p 0) +
        (-a * Real.sin (p 1)) • revolutionAxis := by
  simpa using polarCompactification_partial R a C p 1

theorem polarCompactification_boundary (R a C θ : ℝ) :
    polarCompactification R a C ![θ, 0] =
      (-R) • revolutionRadial θ + (C + a) • revolutionAxis := by
  simp [polarCompactification]

theorem polarCompactification_boundary_partials (R a C θ : ℝ) :
    coordPartial 0 (polarCompactification R a C) ![θ, 0] = (-R) • revolutionAngular θ ∧
    coordPartial 1 (polarCompactification R a C) ![θ, 0] = a • revolutionRadial θ := by
  constructor
  · simp [polarCompactification_partial_theta]
  · simp [polarCompactification_partial_transverse]

end
end TightVer401
