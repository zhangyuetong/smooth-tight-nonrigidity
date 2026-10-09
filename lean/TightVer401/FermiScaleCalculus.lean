import TightVer401.FermiNormalGeometry
import TightVer401.ScalarCoordinateCalculus

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff Matrix
set_option backward.isDefEq.respectTransparency false

def fermiNormalScaleTransverse (κ : ℝ → ℝ) (p : Coord) : ℝ :=
  -Real.sin (p 1) + κ (p 0) * Real.cos (p 1)

theorem fermiNormalScale_contDiff {κ : ℝ → ℝ} (hκ : ContDiff ℝ ∞ κ) :
    ContDiff ℝ ∞ (fermiNormalScale κ) :=
  (Real.contDiff_cos.comp (contDiff_apply ℝ ℝ 1)).add
    ((hκ.comp (contDiff_apply ℝ ℝ 0)).mul
      (Real.contDiff_sin.comp (contDiff_apply ℝ ℝ 1)))

theorem fermiNormalScaleTransverse_contDiff {κ : ℝ → ℝ} (hκ : ContDiff ℝ ∞ κ) :
    ContDiff ℝ ∞ (fermiNormalScaleTransverse κ) :=
  (Real.contDiff_sin.comp (contDiff_apply ℝ ℝ 1)).neg.add
    ((hκ.comp (contDiff_apply ℝ ℝ 0)).mul
      (Real.contDiff_cos.comp (contDiff_apply ℝ ℝ 1)))

theorem fermiNormalScale_partials {κ : ℝ → ℝ} (hκ : ContDiff ℝ ∞ κ) (p : Coord) :
    coordPartial 0 (fermiNormalScale κ) p = deriv κ (p 0) * Real.sin (p 1) ∧
    coordPartial 1 (fermiNormalScale κ) p = fermiNormalScaleTransverse κ p := by
  have hk := ((hκ.differentiable (by simp) (p 0)).hasDerivAt.hasFDerivAt).comp p
    (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)).hasFDerivAt
  have hc := (Real.hasDerivAt_cos (p 1)).hasFDerivAt.comp p
    (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)).hasFDerivAt
  have hs := (Real.hasDerivAt_sin (p 1)).hasFDerivAt.comp p
    (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)).hasFDerivAt
  have hd := hc.add (hk.mul hs)
  have he : (Real.cos ∘ (ContinuousLinearMap.proj (R := ℝ) 1 : Coord →L[ℝ] ℝ) +
      (κ ∘ (ContinuousLinearMap.proj (R := ℝ) 0 : Coord →L[ℝ] ℝ)) *
        (Real.sin ∘ (ContinuousLinearMap.proj (R := ℝ) 1 : Coord →L[ℝ] ℝ))) =
        fermiNormalScale κ := rfl
  rw [he] at hd
  constructor
  · change fderiv ℝ (fermiNormalScale κ) p (Pi.single 0 1) = _
    rw [hd.fderiv]
    simp [ContinuousLinearMap.comp_apply, fermiNormalScale, mul_comm]
  · change fderiv ℝ (fermiNormalScale κ) p (Pi.single 1 1) = _
    rw [hd.fderiv]
    simp [ContinuousLinearMap.comp_apply, fermiNormalScaleTransverse, mul_comm]

theorem fermiNormalScaleTransverse_partials {κ : ℝ → ℝ}
    (hκ : ContDiff ℝ ∞ κ) (p : Coord) :
    coordPartial 0 (fermiNormalScaleTransverse κ) p = deriv κ (p 0) * Real.cos (p 1) ∧
    coordPartial 1 (fermiNormalScaleTransverse κ) p = -fermiNormalScale κ p := by
  have hk := ((hκ.differentiable (by simp) (p 0)).hasDerivAt.hasFDerivAt).comp p
    (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)).hasFDerivAt
  have hc := (Real.hasDerivAt_cos (p 1)).hasFDerivAt.comp p
    (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)).hasFDerivAt
  have hs := (Real.hasDerivAt_sin (p 1)).hasFDerivAt.comp p
    (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)).hasFDerivAt
  have hd := hs.neg.add (hk.mul hc)
  have he : (-(Real.sin ∘ (ContinuousLinearMap.proj (R := ℝ) 1 : Coord →L[ℝ] ℝ)) +
      (κ ∘ (ContinuousLinearMap.proj (R := ℝ) 0 : Coord →L[ℝ] ℝ)) *
        (Real.cos ∘ (ContinuousLinearMap.proj (R := ℝ) 1 : Coord →L[ℝ] ℝ))) =
        fermiNormalScaleTransverse κ := rfl
  rw [he] at hd
  constructor
  · change fderiv ℝ (fermiNormalScaleTransverse κ) p (Pi.single 0 1) = _
    rw [hd.fderiv]
    simp [ContinuousLinearMap.comp_apply, fermiNormalScaleTransverse, mul_comm]
  · change fderiv ℝ (fermiNormalScaleTransverse κ) p (Pi.single 1 1) = _
    rw [hd.fderiv]
    simp [ContinuousLinearMap.comp_apply, fermiNormalScale]
    ring

theorem fermiNormalScale_seam {κ : ℝ → ℝ} (hκ : ContDiff ℝ ∞ κ) (r : ℝ) :
    fermiNormalScale κ ![r,0] = 1 ∧
    coordPartial 0 (fermiNormalScale κ) ![r,0] = 0 ∧
    coordPartial 1 (fermiNormalScale κ) ![r,0] = κ r ∧
    coordPartial 1 (coordPartial 1 (fermiNormalScale κ)) ![r,0] = -1 ∧
    coordPartial 0 (coordPartial 1 (fermiNormalScale κ)) ![r,0] = deriv κ r := by
  have ht : coordPartial 1 (fermiNormalScale κ) = fermiNormalScaleTransverse κ :=
    funext fun p => (fermiNormalScale_partials hκ p).2
  rw [ht]
  simp [fermiNormalScale, fermiNormalScaleTransverse,
    (fermiNormalScale_partials hκ ![r,0]).1,
    (fermiNormalScaleTransverse_partials hκ ![r,0]).1,
    (fermiNormalScaleTransverse_partials hκ ![r,0]).2]

end
end TightVer401
