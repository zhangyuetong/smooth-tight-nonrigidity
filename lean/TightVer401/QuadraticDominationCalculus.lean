import TightVer401.ScalarCoordinateCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Actual cylinder derivatives of the explicit quadratic filler. -/
namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

def dualQuadraticFiller (R M : ℝ) (chi h b : ℝ → ℝ) (p : Coord) : ℝ :=
  -M / 2 * (p 0 - R)^2 + chi (p 0) * (h (p 1) + (p 0 - R) * b (p 1))

theorem dualQuadraticFiller_contDiff (R M : ℝ) {chi h b : ℝ → ℝ}
    (hchi : ContDiff ℝ ∞ chi) (hh : ContDiff ℝ ∞ h) (hb : ContDiff ℝ ∞ b) :
    ContDiff ℝ ∞ (dualQuadraticFiller R M chi h b) := by
  unfold dualQuadraticFiller
  exact (contDiff_const.mul ((contDiff_apply ℝ ℝ 0).sub contDiff_const |>.pow 2)).add
    ((hchi.comp (contDiff_apply ℝ ℝ 0)).mul
      ((hh.comp (contDiff_apply ℝ ℝ 1)).add
        (((contDiff_apply ℝ ℝ 0).sub contDiff_const).mul
          (hb.comp (contDiff_apply ℝ ℝ 1)))))

theorem dualQuadraticFiller_coordPartial (R M : ℝ) {chi h b : ℝ → ℝ}
    (hchi : ContDiff ℝ ∞ chi) (hh : ContDiff ℝ ∞ h) (hb : ContDiff ℝ ∞ b)
    (p : Coord) (i : Fin 2) :
    coordPartial i (dualQuadraticFiller R M chi h b) p =
      if i = 0 then
        -M * (p 0 - R) + deriv chi (p 0) * (h (p 1) + (p 0 - R) * b (p 1)) +
          chi (p 0) * b (p 1)
      else chi (p 0) * (deriv h (p 1) + (p 0 - R) * deriv b (p 1)) := by
  have hr := (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)).hasFDerivAt (x := p)
  have ht := (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)).hasFDerivAt (x := p)
  have hc := (hchi.differentiable (by simp)).differentiableAt.hasDerivAt.hasFDerivAt.comp p hr
  have hd := (hh.differentiable (by simp)).differentiableAt.hasDerivAt.hasFDerivAt.comp p ht
  have he := (hb.differentiable (by simp)).differentiableAt.hasDerivAt.hasFDerivAt.comp p ht
  have hf := ((hr.sub_const R).pow 2 |>.const_mul (-M / 2)).add
    (hc.mul (hd.add ((hr.sub_const R).mul he)))
  change fderiv ℝ (dualQuadraticFiller R M chi h b) p (Pi.single i 1) = _
  rw [show fderiv ℝ (dualQuadraticFiller R M chi h b) p = _ from hf.fderiv]
  fin_cases i <;> simp [ContinuousLinearMap.comp_apply] <;> ring

theorem dualQuadraticFiller_radial_second (R M : ℝ) {chi h b : ℝ → ℝ}
    (hchi : ContDiff ℝ ∞ chi) (hh : ContDiff ℝ ∞ h) (hb : ContDiff ℝ ∞ b) (p : Coord) :
    coordPartial 0 (coordPartial 0 (dualQuadraticFiller R M chi h b)) p =
      -M + deriv (deriv chi) (p 0) * (h (p 1) + (p 0 - R) * b (p 1)) +
        2 * deriv chi (p 0) * b (p 1) := by
  have heq : coordPartial 0 (dualQuadraticFiller R M chi h b) = _ :=
    funext (fun q => dualQuadraticFiller_coordPartial R M hchi hh hb q 0)
  simp only [ite_true] at heq
  rw [heq]
  have hr := (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)).hasFDerivAt (x := p)
  have ht := (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)).hasFDerivAt (x := p)
  have hc := ((contDiff_infty_iff_deriv.mp hchi).2.differentiable (by simp)).differentiableAt.hasDerivAt.hasFDerivAt.comp p hr
  have hd := (hh.differentiable (by simp)).differentiableAt.hasDerivAt.hasFDerivAt.comp p ht
  have he := (hb.differentiable (by simp)).differentiableAt.hasDerivAt.hasFDerivAt.comp p ht
  have hc0 := (hchi.differentiable (by simp)).differentiableAt.hasDerivAt.hasFDerivAt.comp p hr
  have hf := ((hr.sub_const R).const_mul (-M)).add
    (hc.mul (hd.add ((hr.sub_const R).mul he))) |>.add (hc0.mul he)
  change HasFDerivAt (fun q : Coord => -M * (q 0 - R) + deriv chi (q 0) * (h (q 1) + (q 0 - R) * b (q 1)) + chi (q 0) * b (q 1)) _ p at hf
  change fderiv ℝ _ p (Pi.single 0 1) = _
  rw [hf.fderiv]
  simp [ContinuousLinearMap.comp_apply]
  ring

theorem dualQuadraticFiller_angular_second (R M : ℝ) {chi h b : ℝ → ℝ}
    (hchi : ContDiff ℝ ∞ chi) (hh : ContDiff ℝ ∞ h) (hb : ContDiff ℝ ∞ b) (p : Coord) :
    coordPartial 1 (coordPartial 1 (dualQuadraticFiller R M chi h b)) p =
      chi (p 0) * (deriv (deriv h) (p 1) + (p 0 - R) * deriv (deriv b) (p 1)) := by
  have heq : coordPartial 1 (dualQuadraticFiller R M chi h b) = _ :=
    funext (fun q => dualQuadraticFiller_coordPartial R M hchi hh hb q 1)
  simp only [show (1 : Fin 2) ≠ 0 by decide, ite_false] at heq
  rw [heq]
  have hr := (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)).hasFDerivAt (x := p)
  have ht := (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)).hasFDerivAt (x := p)
  have hc := (hchi.differentiable (by simp)).differentiableAt.hasDerivAt.hasFDerivAt.comp p hr
  have hd := ((contDiff_infty_iff_deriv.mp hh).2.differentiable (by simp)).differentiableAt.hasDerivAt.hasFDerivAt.comp p ht
  have he := ((contDiff_infty_iff_deriv.mp hb).2.differentiable (by simp)).differentiableAt.hasDerivAt.hasFDerivAt.comp p ht
  have hf := hc.mul (hd.add ((hr.sub_const R).mul he))
  change HasFDerivAt (fun q : Coord => chi (q 0) * (deriv h (q 1) + (q 0 - R) * deriv b (q 1))) _ p at hf
  change fderiv ℝ _ p (Pi.single 1 1) = _
  rw [hf.fderiv]
  simp [ContinuousLinearMap.comp_apply]
  ring

end
end TightVer401
