import TightVer401.SeamChartHessian
import TightVer401.ScalarCoordinateCalculus

/-! Actual differential data for the polar coordinate map used by ver500.
The angular coordinate is a real lift, so no global inverse angle is assumed. -/
namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff Matrix
set_option backward.isDefEq.respectTransparency false

def saddlePolarChart (p : Coord) : Coord :=
  ![p 0 * Real.cos (p 1), p 0 * Real.sin (p 1)]

theorem saddlePolarChart_contDiff : ContDiff ℝ ∞ saddlePolarChart := by
  apply contDiff_pi.mpr
  intro a
  fin_cases a
  · exact (contDiff_apply ℝ ℝ 0).mul (Real.contDiff_cos.comp (contDiff_apply ℝ ℝ 1))
  · exact (contDiff_apply ℝ ℝ 0).mul (Real.contDiff_sin.comp (contDiff_apply ℝ ℝ 1))

theorem saddlePolarChart_coordPartial (p : Coord) (a i : Fin 2) :
    coordPartial i (fun q => saddlePolarChart q a) p =
      (!![Real.cos (p 1), -p 0 * Real.sin (p 1);
          Real.sin (p 1), p 0 * Real.cos (p 1)] : Matrix (Fin 2) (Fin 2) ℝ) a i := by
  have hr := (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)).hasFDerivAt (x := p)
  have hc := (Real.hasDerivAt_cos (p 1)).hasFDerivAt.comp p
    (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)).hasFDerivAt
  have hs := (Real.hasDerivAt_sin (p 1)).hasFDerivAt.comp p
    (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)).hasFDerivAt
  fin_cases a
  · change fderiv ℝ (fun q : Coord => q 0 * Real.cos (q 1)) p (Pi.single i 1) = _
    have hd := hr.mul hc
    change HasFDerivAt (fun q : Coord => q 0 * Real.cos (q 1)) _ p at hd
    rw [hd.fderiv]
    fin_cases i <;> simp [ContinuousLinearMap.comp_apply] <;> ring
  · change fderiv ℝ (fun q : Coord => q 0 * Real.sin (q 1)) p (Pi.single i 1) = _
    have hd := hr.mul hs
    change HasFDerivAt (fun q : Coord => q 0 * Real.sin (q 1)) _ p at hd
    rw [hd.fderiv]
    fin_cases i <;> simp [ContinuousLinearMap.comp_apply] <;> ring

theorem saddlePolarChart_jacobian (p : Coord) :
    seamCoordinateJacobian saddlePolarChart p =
      !![Real.cos (p 1), -p 0 * Real.sin (p 1);
         Real.sin (p 1), p 0 * Real.cos (p 1)] := by
  ext a i
  exact saddlePolarChart_coordPartial p a i

theorem saddlePolarChart_jacobian_det (p : Coord) :
    (seamCoordinateJacobian saddlePolarChart p).det = p 0 := by
  rw [saddlePolarChart_jacobian, Matrix.det_fin_two]
  simp
  linear_combination p 0 * Real.sin_sq_add_cos_sq (p 1)

theorem saddlePolarChart_hessian (p : Coord) (a i j : Fin 2) :
    planarHessian (fun q => saddlePolarChart q a) p i j =
      (if a = 0 then
        (!![0, -Real.sin (p 1); -Real.sin (p 1), -p 0 * Real.cos (p 1)] : Matrix (Fin 2) (Fin 2) ℝ)
      else
        (!![0, Real.cos (p 1); Real.cos (p 1), -p 0 * Real.sin (p 1)] : Matrix (Fin 2) (Fin 2) ℝ)) i j := by
  have he : coordPartial j (fun q => saddlePolarChart q a) =
      fun q => (!![Real.cos (q 1), -q 0 * Real.sin (q 1);
                   Real.sin (q 1), q 0 * Real.cos (q 1)] : Matrix (Fin 2) (Fin 2) ℝ) a j := by
    funext q
    exact saddlePolarChart_coordPartial q a j
  unfold planarHessian
  rw [he]
  have hr := (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)).hasFDerivAt (x := p)
  have hc := (Real.hasDerivAt_cos (p 1)).hasFDerivAt.comp p
    (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)).hasFDerivAt
  have hs := (Real.hasDerivAt_sin (p 1)).hasFDerivAt.comp p
    (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)).hasFDerivAt
  fin_cases a <;> fin_cases j
  · change fderiv ℝ (fun q : Coord => Real.cos (q 1)) p (Pi.single i 1) = _
    change HasFDerivAt (fun q : Coord => Real.cos (q 1)) _ p at hc
    rw [hc.fderiv]
    fin_cases i <;> simp [ContinuousLinearMap.comp_apply]
  · change fderiv ℝ (fun q : Coord => -q 0 * Real.sin (q 1)) p (Pi.single i 1) = _
    have hd := hr.neg.mul hs
    change HasFDerivAt (fun q : Coord => -q 0 * Real.sin (q 1)) _ p at hd
    rw [hd.fderiv]
    fin_cases i <;> simp [ContinuousLinearMap.comp_apply] <;> ring
  · change fderiv ℝ (fun q : Coord => Real.sin (q 1)) p (Pi.single i 1) = _
    change HasFDerivAt (fun q : Coord => Real.sin (q 1)) _ p at hs
    rw [hs.fderiv]
    fin_cases i <;> simp [ContinuousLinearMap.comp_apply]
  · change fderiv ℝ (fun q : Coord => q 0 * Real.cos (q 1)) p (Pi.single i 1) = _
    have hd := hr.mul hc
    change HasFDerivAt (fun q : Coord => q 0 * Real.cos (q 1)) _ p at hd
    rw [hd.fderiv]
    fin_cases i <;> simp [ContinuousLinearMap.comp_apply] <;> ring

end
end TightVer401
