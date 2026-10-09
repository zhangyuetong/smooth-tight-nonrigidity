import TightVer401.CorrugatedSeedVisiblePairs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

namespace TightVer401
noncomputable section
open scoped RealInnerProductSpace ContDiff

theorem corrugated_visibility_sqrt_ratio {R r : ℝ} (hR : 0 ≤ R) (hr : R < r) :
    Real.sqrt (1 - (R / r)^2) = Real.sqrt (r^2 - R^2) / r := by
  have hrp : 0 < r := hR.trans_lt hr
  have he : 1 - (R / r)^2 = (r^2 - R^2) / r^2 := by
    field_simp
  rw [he, Real.sqrt_div (by nlinarith : 0 ≤ r^2 - R^2), Real.sqrt_sq hrp.le]

theorem corrugatedVisibilityCoefficient_exp_arccos {R r : ℝ} (hR : 0 ≤ R) (hr : R < r) :
    corrugatedVisibilityCoefficient R r = Complex.exp ((Real.arccos (R / r) : ℂ) * Complex.I) := by
  have hrp : 0 < r := hR.trans_lt hr
  rw [Complex.exp_mul_I]
  unfold corrugatedVisibilityCoefficient
  have hl : (-1 : ℝ) ≤ R / r := by have := div_nonneg hR hrp.le; linarith
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_arccos hl ((div_le_one hrp).mpr hr.le), Real.sin_arccos,
    corrugated_visibility_sqrt_ratio hR hr]

theorem corrugated_visibility_inner_formula {R : ℝ} (hR : 0 ≤ R) {z : ℂ}
    (hz : R < ‖z‖) (v : ℂ) :
    inner ℝ v (corrugatedVisibilityDirection R z) / Real.sqrt (‖z‖^2 - R^2) =
      (v / z).im + R * inner ℝ z v / (‖z‖^2 * Real.sqrt (‖z‖^2 - R^2)) := by
  have hn : 0 < ‖z‖ := hR.trans_lt hz
  have hzne : z ≠ 0 := norm_pos_iff.mp hn
  have hs : 0 < Real.sqrt (‖z‖^2 - R^2) := Real.sqrt_pos.mpr (by nlinarith)
  rw [corrugatedVisibilityDirection_eq hzne]
  simp only [corrugated_complex_inner, Complex.div_im, Complex.normSq_eq_norm_sq,
    corrugatedVisibilityCoefficient, Complex.real_smul, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero,
    sub_zero, zero_add, add_zero, mul_one]
  field_simp
  ring

theorem corrugated_complex_norm_hasDerivAt {f : ℝ → ℂ} {v : ℂ} {t : ℝ}
    (hf : HasDerivAt f v t) (hne : f t ≠ 0) :
    HasDerivAt (fun s => ‖f s‖) (inner ℝ (f t) v / ‖f t‖) t := by
  have hn : 0 < ‖f t‖ := norm_pos_iff.mpr hne
  have h := hf.norm_sq.sqrt (pow_ne_zero 2 (ne_of_gt hn))
  have h' := h.congr_of_eventuallyEq (f₁ := fun s => ‖f s‖)
    (Filter.Eventually.of_forall (fun s => (Real.sqrt_sq (norm_nonneg (f s))).symm))
  have he : (2 * inner ℝ (f t) v) / (2 * Real.sqrt (‖f t‖^2)) =
      inner ℝ (f t) v / ‖f t‖ := by rw [Real.sqrt_sq (norm_nonneg _)]; field_simp
  exact he ▸ h'

theorem corrugated_visibility_arccos_hasDerivAt {f : ℝ → ℂ} {v : ℂ} {t R : ℝ}
    (hf : HasDerivAt f v t) (hR : 0 ≤ R) (hr : R < ‖f t‖) :
    HasDerivAt (fun s => Real.arccos (R / ‖f s‖))
      (R * inner ℝ (f t) v / (‖f t‖^2 * Real.sqrt (‖f t‖^2 - R^2))) t := by
  have hn : 0 < ‖f t‖ := hR.trans_lt hr
  have hl : (-1 : ℝ) < R / ‖f t‖ := by
    have : 0 ≤ R / ‖f t‖ := div_nonneg hR hn.le
    linarith
  have hu : R / ‖f t‖ < 1 := (div_lt_one hn).mpr hr
  have hnorm := corrugated_complex_norm_hasDerivAt hf (norm_pos_iff.mp hn)
  have hq := (hasDerivAt_const t R).div hnorm (ne_of_gt hn)
  simp only [zero_mul, zero_sub] at hq
  have h := (Real.hasDerivAt_arccos (ne_of_gt hl) (ne_of_lt hu)).comp t hq
  have h' := h.congr_of_eventuallyEq (f₁ := fun s => Real.arccos (R / ‖f s‖))
    (Filter.Eventually.of_forall (fun _ => rfl))
  have hs : 0 < Real.sqrt (‖f t‖^2 - R^2) := Real.sqrt_pos.mpr (by nlinarith)
  have he : -(1 / Real.sqrt (1 - (R / ‖f t‖)^2)) *
      (-(R * (inner ℝ (f t) v / ‖f t‖)) / ‖f t‖^2) =
      R * inner ℝ (f t) v / (‖f t‖^2 * Real.sqrt (‖f t‖^2 - R^2)) := by
    rw [corrugated_visibility_sqrt_ratio hR hr]
    field_simp
  exact he ▸ h'

end
end TightVer401
