import TightVer401.MomentDivergenceBounds

namespace TightVer401
noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

theorem momentDivergence_path_lower {n : ℕ} {b χ g : ℝ → ℝ} {c : Fin n → ℝ}
    {ψ : Fin n → ℝ → ℝ} {L u v δ t : ℝ}
    (hb : ContDiff ℝ ∞ b) (hχ : ContDiff ℝ ∞ χ) (hψ : ∀ j, ContDiff ℝ ∞ (ψ j))
    (hg : Continuous g) (hbpos : ∀ r, 0 < b r) (hδ : 0 < δ)
    (hχbound : ∀ r, 0 ≤ χ r ∧ χ r ≤ 1)
    (hdisjoint : ∀ r, χ r ≠ 0 → ∀ j, ψ j r = 0)
    (hcontrol : ∀ r, χ r = 0 → δ ≤ b r - ∑ j, |c j| * |ψ j r|)
    (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ L)
    (hplateau : ∀ r ∈ Icc u v, χ r = 1)
    (hgsign : ∀ r ∈ Icc 0 L, χ r ≠ 0 → 0 ≤ g r)
    (ht : 0 ≤ t) (ht1 : t < 1) :
    (Real.sqrt (1 - t))⁻¹ * (∫ r in u..v, g r / Real.sqrt (b r)) -
      (∫ r in 0..L, |g r| / Real.sqrt δ) ≤
      momentNonlinearPeriod (momentPath b χ c ψ t) g L := by
  have hpos (r) : 0 < momentPath b χ c ψ t r :=
    momentPath_pos ht ht1 (hbpos r) (hχbound r) (hdisjoint r)
      (fun hz => by have hbnd := hcontrol r hz; linarith)
  let f := fun r => g r / Real.sqrt (momentPath b χ c ψ t r)
  let h := fun r => |g r| / Real.sqrt δ
  let p := fun r => g r / Real.sqrt (b r)
  have hf : Continuous f := hg.div
    (Real.continuous_sqrt.comp (momentPath_contDiff c hb hχ hψ t).continuous)
    (fun r => ne_of_gt (Real.sqrt_pos.mpr (hpos r)))
  have hh : Continuous h := hg.abs.div_const _
  have hp : Continuous p := hg.div (Real.continuous_sqrt.comp hb.continuous)
    (fun r => ne_of_gt (Real.sqrt_pos.mpr (hbpos r)))
  have hmajor : ∀ r ∈ Icc 0 L, -h r ≤ f r := by
    intro r hr
    by_cases hz : χ r = 0
    · have hbnd := momentDivergence_control_lower ht ht1.le hz (hcontrol r hz)
      simpa only [f, h, neg_div] using momentDivergence_scalar_lower (g := g r) hδ hbnd
    · have hfnonneg : 0 ≤ f r := div_nonneg (hgsign r hr hz) (Real.sqrt_nonneg _)
      have hhnonneg : 0 ≤ h r := div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
      linarith
  have hhnonneg : ∀ r ∈ Icc 0 L, 0 ≤ h r :=
    fun r _ => div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  have hplateauf : ∀ r ∈ uIcc u v, f r = (Real.sqrt (1 - t))⁻¹ * p r := by
    intro r hr
    rw [uIcc_of_le huv] at hr
    have hχone := hplateau r hr
    have hC : momentPathCorrection c ψ r = 0 := by
      simp [momentPathCorrection, hdisjoint r (by rw [hχone]; norm_num)]
    have hvalue : momentPath b χ c ψ t r = (1 - t) * b r := by
      rw [momentPath, hχone, hC]
      ring
    dsimp [f, p]
    rw [hvalue, Real.sqrt_mul (by linarith : 0 ≤ 1 - t)]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  exact momentDivergence_interval_lower hu huv hv hf hh hp hmajor hhnonneg hplateauf

theorem momentDivergence_path_unbounded {n : ℕ} {b χ g : ℝ → ℝ} {c : Fin n → ℝ}
    {ψ : Fin n → ℝ → ℝ} {L u v δ : ℝ}
    (hb : ContDiff ℝ ∞ b) (hχ : ContDiff ℝ ∞ χ) (hψ : ∀ j, ContDiff ℝ ∞ (ψ j))
    (hg : Continuous g) (hbpos : ∀ r, 0 < b r) (hδ : 0 < δ)
    (hχbound : ∀ r, 0 ≤ χ r ∧ χ r ≤ 1)
    (hdisjoint : ∀ r, χ r ≠ 0 → ∀ j, ψ j r = 0)
    (hcontrol : ∀ r, χ r = 0 → δ ≤ b r - ∑ j, |c j| * |ψ j r|)
    (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ L)
    (hplateau : ∀ r ∈ Icc u v, χ r = 1)
    (hgsign : ∀ r ∈ Icc 0 L, χ r ≠ 0 → 0 ≤ g r)
    (hgpos : ∀ r ∈ Icc u v, 0 < g r) (M : ℝ) :
    ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧ M < momentNonlinearPeriod (momentPath b χ c ψ t) g L := by
  have hC := momentDivergence_plateau_positive hb.continuous hg hbpos huv hgpos
  obtain ⟨t, ht, ht1, hM⟩ := momentDivergence_scale_unbounded hC
    (B := ∫ r in 0..L, |g r| / Real.sqrt δ) M
  exact ⟨t, ht, ht1, hM.trans_le (momentDivergence_path_lower hb hχ hψ hg hbpos hδ
    hχbound hdisjoint hcontrol hu huv.le hv hplateau hgsign ht ht1)⟩

end
end TightVer401
