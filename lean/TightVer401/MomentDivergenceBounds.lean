import TightVer401.MomentDivergenceScale
import TightVer401.MomentPath

namespace TightVer401
noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

theorem momentDivergence_scalar_lower {g A δ : ℝ} (hδ : 0 < δ) (hA : δ ≤ A) :
    -|g| / Real.sqrt δ ≤ g / Real.sqrt A := by
  have hrδ := Real.sqrt_pos.mpr hδ
  have hrA := Real.sqrt_pos.mpr (hδ.trans_le hA)
  have hnorm : |g| / Real.sqrt A ≤ |g| / Real.sqrt δ :=
    div_le_div_of_nonneg_left (abs_nonneg g) hrδ (Real.sqrt_le_sqrt hA)
  calc
    -|g| / Real.sqrt δ ≤ -|g| / Real.sqrt A := by
      simpa only [neg_div] using neg_le_neg hnorm
    _ ≤ g / Real.sqrt A := div_le_div_of_nonneg_right (neg_abs_le g) hrA.le

theorem momentDivergence_control_lower {n : ℕ} {b χ : ℝ → ℝ} {c : Fin n → ℝ}
    {ψ : Fin n → ℝ → ℝ} {t r δ : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hχ : χ r = 0) (hδ : δ ≤ b r - ∑ j, |c j| * |ψ j r|) :
    δ ≤ momentPath b χ c ψ t r := by
  have hsum : 0 ≤ ∑ j, |c j| * |ψ j r| := by positivity
  have hC := momentPathCorrection_abs_le c ψ r
  have htc : |t * momentPathCorrection c ψ r| ≤ ∑ j, |c j| * |ψ j r| := by
    rw [abs_mul, abs_of_nonneg ht]
    exact (mul_le_mul_of_nonneg_left hC ht).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right ht1 hsum)
  have hlo := neg_abs_le (t * momentPathCorrection c ψ r)
  simp only [momentPath, hχ, mul_zero, zero_mul, sub_zero]
  linarith

theorem momentDivergence_interval_lower {f h p : ℝ → ℝ} {L u v C : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ L)
    (hf : Continuous f) (hh : Continuous h) (hp : Continuous p)
    (hmajor : ∀ r ∈ Icc 0 L, -h r ≤ f r)
    (hhnonneg : ∀ r ∈ Icc 0 L, 0 ≤ h r)
    (hplateau : ∀ r ∈ uIcc u v, f r = C * p r) :
    C * (∫ r in u..v, p r) - (∫ r in 0..L, h r) ≤ ∫ r in 0..L, f r := by
  have hi₁ : -(∫ r in 0..u, h r) ≤ ∫ r in 0..u, f r := by
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_mono_on hu ((hh.neg).intervalIntegrable 0 u)
      (hf.intervalIntegrable 0 u) (fun r hr => hmajor r ⟨hr.1, hr.2.trans (huv.trans hv)⟩)
  have hi₂ : -(∫ r in v..L, h r) ≤ ∫ r in v..L, f r := by
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_mono_on hv ((hh.neg).intervalIntegrable v L)
      (hf.intervalIntegrable v L) (fun r hr => hmajor r ⟨(hu.trans huv).trans hr.1, hr.2⟩)
  have hmiddle : (∫ r in u..v, f r) = C * (∫ r in u..v, p r) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    exact hplateau
  have hmidpos : 0 ≤ ∫ r in u..v, h r :=
    intervalIntegral.integral_nonneg huv (fun r hr => hhnonneg r ⟨hu.trans hr.1, hr.2.trans hv⟩)
  have hfsplit : (∫ r in 0..u, f r) + (∫ r in u..v, f r) + (∫ r in v..L, f r) =
      ∫ r in 0..L, f r := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable 0 u)
      (hf.intervalIntegrable u v), intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable 0 v) (hf.intervalIntegrable v L)]
  have hhsplit : (∫ r in 0..u, h r) + (∫ r in u..v, h r) + (∫ r in v..L, h r) =
      ∫ r in 0..L, h r := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hh.intervalIntegrable 0 u)
      (hh.intervalIntegrable u v), intervalIntegral.integral_add_adjacent_intervals
      (hh.intervalIntegrable 0 v) (hh.intervalIntegrable v L)]
  linarith

theorem momentDivergence_plateau_positive {b g : ℝ → ℝ} {u v : ℝ}
    (hb : Continuous b) (hg : Continuous g) (hpos : ∀ r, 0 < b r)
    (huv : u < v) (hgpos : ∀ r ∈ Icc u v, 0 < g r) :
    0 < ∫ r in u..v, g r / Real.sqrt (b r) := by
  apply intervalIntegral.integral_pos huv
    ((hg.div (Real.continuous_sqrt.comp hb)
      (fun r => ne_of_gt (Real.sqrt_pos.mpr (hpos r)))).continuousOn)
  · intro r hr
    exact (div_pos (hgpos r ⟨hr.1.le, hr.2⟩) (Real.sqrt_pos.mpr (hpos r))).le
  · exact ⟨u, ⟨le_rfl, huv.le⟩, div_pos (hgpos u ⟨le_rfl, huv.le⟩)
      (Real.sqrt_pos.mpr (hpos u))⟩

end
end TightVer401
