import TightVer401.MomentDivergenceSigned

namespace TightVer401
noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

theorem momentDivergence_path_upper {n : ℕ} {b χ g : ℝ → ℝ} {c : Fin n → ℝ}
    {ψ : Fin n → ℝ → ℝ} {L u v δ t : ℝ}
    (hb : ContDiff ℝ ∞ b) (hχ : ContDiff ℝ ∞ χ) (hψ : ∀ j, ContDiff ℝ ∞ (ψ j))
    (hg : Continuous g) (hbpos : ∀ r, 0 < b r) (hδ : 0 < δ)
    (hχbound : ∀ r, 0 ≤ χ r ∧ χ r ≤ 1)
    (hdisjoint : ∀ r, χ r ≠ 0 → ∀ j, ψ j r = 0)
    (hcontrol : ∀ r, χ r = 0 → δ ≤ b r - ∑ j, |c j| * |ψ j r|)
    (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ L)
    (hplateau : ∀ r ∈ Icc u v, χ r = 1)
    (hgsign : ∀ r ∈ Icc 0 L, χ r ≠ 0 → g r ≤ 0)
    (ht : 0 ≤ t) (ht1 : t < 1) :
    momentNonlinearPeriod (momentPath b χ c ψ t) g L ≤
      (Real.sqrt (1 - t))⁻¹ * (∫ r in u..v, g r / Real.sqrt (b r)) +
      (∫ r in 0..L, |g r| / Real.sqrt δ) := by
  have hlo := momentDivergence_path_lower hb hχ hψ hg.neg hbpos hδ
    hχbound hdisjoint hcontrol hu huv hv hplateau
    (fun r hr hz => neg_nonneg.mpr (hgsign r hr hz)) ht ht1
  have hplateauneg : (∫ r in u..v, -g r / Real.sqrt (b r)) =
      -(∫ r in u..v, g r / Real.sqrt (b r)) := by
    simp only [neg_div, intervalIntegral.integral_neg]
  simp only [momentDivergence_period_neg, Pi.neg_apply, abs_neg] at hlo
  rw [hplateauneg] at hlo
  linarith

end
end TightVer401
