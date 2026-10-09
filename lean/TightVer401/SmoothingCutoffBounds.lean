import TightVer401.SmoothingCutoff
import Mathlib.Analysis.Matrix.Normed

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff Matrix.Norms.Elementwise

def smoothingCutoffHessianError (χ F G : Coord → ℝ) (p : Coord) : Matrix (Fin 2) (Fin 2) ℝ :=
  planarHessian (smoothingCutoffBlend χ F G) p -
    ((1 - χ p) • planarHessian G p + χ p • planarHessian F p)

theorem smoothingCutoffHessianError_apply {χ F G : Coord → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (p : Coord) (i j : Fin 2) :
    smoothingCutoffHessianError χ F G p i j =
      coordPartial i χ p * (coordPartial j F p - coordPartial j G p) +
      coordPartial j χ p * (coordPartial i F p - coordPartial i G p) +
      (F p - G p) * planarHessian χ p i j := by
  change planarHessian (smoothingCutoffBlend χ F G) p i j -
    ((1 - χ p) * planarHessian G p i j + χ p * planarHessian F p i j) = _
  rw [smoothingCutoffBlend_hessian hχ hF hG]
  ring

theorem smoothingCutoffHessianError_entry_bound {χ F G : Coord → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    {p : Coord} {A B u v : ℝ} (hA : 0 ≤ A)
    (hχ₁ : ∀ i, |coordPartial i χ p| ≤ A) (hχ₂ : ∀ i j, |planarHessian χ p i j| ≤ B)
    (hval : |F p - G p| ≤ u) (hgrad : ∀ i, |coordPartial i F p - coordPartial i G p| ≤ v)
    (i j : Fin 2) : |smoothingCutoffHessianError χ F G p i j| ≤ 2 * A * v + u * B := by
  rw [smoothingCutoffHessianError_apply hχ hF hG]
  calc
    _ ≤ |coordPartial i χ p * (coordPartial j F p - coordPartial j G p)| +
        |coordPartial j χ p * (coordPartial i F p - coordPartial i G p)| +
        |(F p - G p) * planarHessian χ p i j| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ A * v + A * v + u * B := by
      simp only [abs_mul]
      apply add_le_add
      · exact add_le_add (mul_le_mul (hχ₁ i) (hgrad j) (abs_nonneg _) hA)
          (mul_le_mul (hχ₁ j) (hgrad i) (abs_nonneg _) hA)
      · exact mul_le_mul hval (hχ₂ i j) (abs_nonneg _) (by linarith [hval, abs_nonneg (F p - G p)])
    _ = _ := by ring

theorem smoothingCutoffHessianError_norm_bound {χ F G : Coord → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    {p : Coord} {A B u v : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hχ₁ : ∀ i, |coordPartial i χ p| ≤ A) (hχ₂ : ∀ i j, |planarHessian χ p i j| ≤ B)
    (hval : |F p - G p| ≤ u) (hgrad : ∀ i, |coordPartial i F p - coordPartial i G p| ≤ v) :
    ‖smoothingCutoffHessianError χ F G p‖ ≤ 2 * A * v + u * B := by
  have hb : 0 ≤ 2 * A * v + u * B := by positivity
  apply (pi_norm_le_iff_of_nonneg hb).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg hb).mpr
  intro j
  rw [Real.norm_eq_abs]
  exact smoothingCutoffHessianError_entry_bound hχ hF hG hA hχ₁ hχ₂ hval hgrad i j

end
end TightVer401
