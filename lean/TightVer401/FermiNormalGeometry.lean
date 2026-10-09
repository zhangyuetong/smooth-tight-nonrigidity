import TightVer401.NormalLoopActual
import TightVer401.RuledNormal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

def fermiNormalMap (ζ : ℝ → Ambient) (p : Coord) : Ambient :=
  Real.cos (p 1) • ζ (p 0) + Real.sin (p 1) • normalLoopTangent ζ (p 0)

def fermiNormalScale (κ : ℝ → ℝ) (p : Coord) : ℝ :=
  Real.cos (p 1) + κ (p 0) * Real.sin (p 1)

def fermiNormalTransverse (ζ : ℝ → Ambient) (p : Coord) : Ambient :=
  -Real.sin (p 1) • ζ (p 0) + Real.cos (p 1) • normalLoopTangent ζ (p 0)

theorem fermiNormalMap_contDiff {ζ : ℝ → Ambient} (hζ : ContDiff ℝ ∞ ζ) :
    ContDiff ℝ ∞ (fermiNormalMap ζ) := by
  have hP := (normalLoop_actual_smooth hζ).1
  exact ((Real.contDiff_cos.comp (contDiff_apply ℝ ℝ 1)).smul
    (hζ.comp (contDiff_apply ℝ ℝ 0))).add
      ((Real.contDiff_sin.comp (contDiff_apply ℝ ℝ 1)).smul
        (hP.comp (contDiff_apply ℝ ℝ 0)))

theorem fermiNormalMap_partials {ζ : ℝ → Ambient} (hζ : ContDiff ℝ ∞ ζ)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1) (p : Coord) :
    coordPartial 0 (fermiNormalMap ζ) p =
      fermiNormalScale (normalLoopCurvature ζ) p • deriv ζ (p 0) ∧
    coordPartial 1 (fermiNormalMap ζ) p = fermiNormalTransverse ζ p := by
  have hζc := ((hζ.differentiable (by simp) (p 0)).hasDerivAt.hasFDerivAt).comp p
    (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)).hasFDerivAt
  have hPc := ((normalLoop_actual_frame hζ hunit hspeed (p 0)).2.1.hasFDerivAt).comp p
    (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)).hasFDerivAt
  have hc := (Real.hasDerivAt_cos (p 1)).hasFDerivAt.comp p
    (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)).hasFDerivAt
  have hs := (Real.hasDerivAt_sin (p 1)).hasFDerivAt.comp p
    (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)).hasFDerivAt
  have hd := (hc.smul hζc).add (hs.smul hPc)
  have hf : (((Real.cos ∘ (ContinuousLinearMap.proj (R := ℝ) 1 : Coord →L[ℝ] ℝ)) •
      (ζ ∘ (ContinuousLinearMap.proj (R := ℝ) 0 : Coord →L[ℝ] ℝ))) +
      (Real.sin ∘ (ContinuousLinearMap.proj (R := ℝ) 1 : Coord →L[ℝ] ℝ)) •
      (normalLoopTangent ζ ∘ (ContinuousLinearMap.proj (R := ℝ) 0 : Coord →L[ℝ] ℝ))) =
      fermiNormalMap ζ := rfl
  rw [hf] at hd
  constructor
  · rw [coordPartial, hd.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply, ContinuousLinearMap.toSpanSingleton_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply,
      Function.comp_apply, Pi.single_eq_same, Pi.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0),
      zero_smul, one_smul, smul_zero, add_zero, zero_add, fermiNormalScale]
    module
  · rw [coordPartial, hd.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply, ContinuousLinearMap.toSpanSingleton_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply,
      Function.comp_apply, Pi.single_eq_same, Pi.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1),
      zero_smul, one_smul, smul_zero, add_zero, zero_add, fermiNormalTransverse]

theorem fermiNormalMap_unit {ζ : ℝ → Ambient} (hζ : ContDiff ℝ ∞ ζ)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1) (p : Coord) :
    inner ℝ (fermiNormalMap ζ p) (fermiNormalMap ζ p) = 1 := by
  have hf := (normalLoop_actual_frame hζ hunit hspeed (p 0)).1
  have hζP : inner ℝ (ζ (p 0)) (normalLoopTangent ζ (p 0)) = 0 := by
    rw [real_inner_comm]
    exact hf.2.2.2.2.1
  simp only [fermiNormalMap, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, hunit, hf.1, hf.2.2.2.2.1, hζP, mul_zero, mul_one, add_zero, zero_add]
  nlinarith [Real.sin_sq_add_cos_sq (p 1)]

theorem fermiNormalMap_metric {ζ : ℝ → Ambient} (hζ : ContDiff ℝ ∞ ζ)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1) (p : Coord) :
    inducedMetric (fermiNormalMap ζ) p =
      !![(fermiNormalScale (normalLoopCurvature ζ) p)^2, 0; 0, 1] := by
  have hf := (normalLoop_actual_frame hζ hunit hspeed (p 0)).1
  have hζP : inner ℝ (ζ (p 0)) (normalLoopTangent ζ (p 0)) = 0 := by
    rw [real_inner_comm]
    exact hf.2.2.2.2.1
  have hEP : inner ℝ (deriv ζ (p 0)) (normalLoopTangent ζ (p 0)) = 0 := by
    rw [real_inner_comm]
    exact hf.2.2.2.1
  have hζE : inner ℝ (ζ (p 0)) (deriv ζ (p 0)) = 0 := by
    rw [real_inner_comm]
    exact hf.2.2.2.2.2
  have hp := fermiNormalMap_partials hζ hunit hspeed p
  ext i j
  fin_cases i <;> fin_cases j
  · change inner ℝ (coordPartial 0 (fermiNormalMap ζ) p)
      (coordPartial 0 (fermiNormalMap ζ) p) =
        (fermiNormalScale (normalLoopCurvature ζ) p)^2
    rw [hp.1]
    simp only [real_inner_smul_left, real_inner_smul_right, hf.2.1, mul_one]
    ring
  · change inner ℝ (coordPartial 0 (fermiNormalMap ζ) p)
      (coordPartial 1 (fermiNormalMap ζ) p) = 0
    rw [hp.1, hp.2]
    simp only [fermiNormalTransverse, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, hf.2.2.2.2.2, hEP, mul_zero, add_zero]
  · change inner ℝ (coordPartial 1 (fermiNormalMap ζ) p)
      (coordPartial 0 (fermiNormalMap ζ) p) = 0
    rw [hp.1, hp.2]
    simp only [fermiNormalTransverse, inner_add_left, real_inner_smul_left,
      real_inner_smul_right, hζE, hf.2.2.2.1, mul_zero, add_zero]
  · change inner ℝ (coordPartial 1 (fermiNormalMap ζ) p)
      (coordPartial 1 (fermiNormalMap ζ) p) = 1
    rw [hp.2]
    simp only [fermiNormalTransverse, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right, hunit, hf.1,
      hf.2.2.2.2.1, hζP, mul_zero, mul_one, add_zero, zero_add]
    nlinarith [Real.sin_sq_add_cos_sq (p 1)]

end
end TightVer401
