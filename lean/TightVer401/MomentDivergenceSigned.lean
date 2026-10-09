import TightVer401.MomentDivergenceAttainment

namespace TightVer401
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

theorem momentDivergence_period_neg (a g : ℝ → ℝ) (L : ℝ) :
    momentNonlinearPeriod a (-g) L = -momentNonlinearPeriod a g L := by
  unfold momentNonlinearPeriod
  simp only [Pi.neg_apply, neg_div, intervalIntegral.integral_neg]

theorem momentDivergence_path_limit {n : ℕ} {b χ g : ℝ → ℝ} {c : Fin n → ℝ}
    {ψ : Fin n → ℝ → ℝ} {L u v δ : ℝ}
    (hb : ContDiff ℝ ∞ b) (hχ : ContDiff ℝ ∞ χ) (hψ : ∀ j, ContDiff ℝ ∞ (ψ j))
    (hg : Continuous g) (hbpos : ∀ r, 0 < b r) (hδ : 0 < δ)
    (hχbound : ∀ r, 0 ≤ χ r ∧ χ r ≤ 1)
    (hdisjoint : ∀ r, χ r ≠ 0 → ∀ j, ψ j r = 0)
    (hcontrol : ∀ r, χ r = 0 → δ ≤ b r - ∑ j, |c j| * |ψ j r|)
    (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ L)
    (hplateau : ∀ r ∈ Icc u v, χ r = 1)
    (hgsign : ∀ r ∈ Icc 0 L, χ r ≠ 0 → 0 ≤ g r)
    (hgpos : ∀ r ∈ Icc u v, 0 < g r) :
    Tendsto (fun t => momentNonlinearPeriod (momentPath b χ c ψ t) g L) (𝓝[<] 1) atTop := by
  let C := ∫ r in u..v, g r / Real.sqrt (b r)
  let B := ∫ r in 0..L, |g r| / Real.sqrt δ
  have hC : 0 < C := momentDivergence_plateau_positive hb.continuous hg hbpos huv hgpos
  have hs : Tendsto (fun t : ℝ => (Real.sqrt (1 - t))⁻¹ * C - B) (𝓝[<] 1) atTop := by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right (𝓝[<] (1 : ℝ)) (-B)
      (momentDivergence_inv_sqrt_limit.atTop_mul_const hC)
  apply tendsto_atTop_mono' (𝓝[<] (1 : ℝ)) _ hs
  have hz : ∀ᶠ t : ℝ in 𝓝[<] 1, 0 < t :=
    (lt_mem_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono inf_le_left
  filter_upwards [hz, self_mem_nhdsWithin] with t ht ht1
  exact momentDivergence_path_lower hb hχ hψ hg hbpos hδ hχbound hdisjoint hcontrol
    hu huv.le hv hplateau hgsign ht.le ht1

theorem momentDivergence_path_attain_below {n : ℕ} {b χ g : ℝ → ℝ} {c : Fin n → ℝ}
    {ψ : Fin n → ℝ → ℝ} {L u v δ B : ℝ}
    (hb : ContDiff ℝ ∞ b) (hχ : ContDiff ℝ ∞ χ) (hψ : ∀ j, ContDiff ℝ ∞ (ψ j))
    (hg : Continuous g) (hbpos : ∀ r, 0 < b r) (hδ : 0 < δ)
    (hχbound : ∀ r, 0 ≤ χ r ∧ χ r ≤ 1)
    (hdisjoint : ∀ r, χ r ≠ 0 → ∀ j, ψ j r = 0)
    (hcontrol : ∀ r, χ r = 0 → δ ≤ b r - ∑ j, |c j| * |ψ j r|)
    (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ L)
    (hplateau : ∀ r ∈ Icc u v, χ r = 1)
    (hgsign : ∀ r ∈ Icc 0 L, χ r ≠ 0 → g r ≤ 0)
    (hgneg : ∀ r ∈ Icc u v, g r < 0)
    (hB : B ≤ momentNonlinearPeriod b g L) :
    ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧ momentNonlinearPeriod (momentPath b χ c ψ t) g L = B := by
  have hBneg : momentNonlinearPeriod b (-g) L ≤ -B := by
    rw [momentDivergence_period_neg]
    exact neg_le_neg hB
  obtain ⟨t, ht, ht1, he⟩ := momentDivergence_path_attain_above
    hb hχ hψ hg.neg hbpos hδ hχbound hdisjoint hcontrol hu huv hv hplateau
    (fun r hr hz => neg_nonneg.mpr (hgsign r hr hz))
    (fun r hr => neg_pos.mpr (hgneg r hr)) hBneg
  rw [momentDivergence_period_neg] at he
  exact ⟨t, ht, ht1, neg_injective he⟩

theorem momentDivergence_path_limit_negative {n : ℕ} {b χ g : ℝ → ℝ} {c : Fin n → ℝ}
    {ψ : Fin n → ℝ → ℝ} {L u v δ : ℝ}
    (hb : ContDiff ℝ ∞ b) (hχ : ContDiff ℝ ∞ χ) (hψ : ∀ j, ContDiff ℝ ∞ (ψ j))
    (hg : Continuous g) (hbpos : ∀ r, 0 < b r) (hδ : 0 < δ)
    (hχbound : ∀ r, 0 ≤ χ r ∧ χ r ≤ 1)
    (hdisjoint : ∀ r, χ r ≠ 0 → ∀ j, ψ j r = 0)
    (hcontrol : ∀ r, χ r = 0 → δ ≤ b r - ∑ j, |c j| * |ψ j r|)
    (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ L)
    (hplateau : ∀ r ∈ Icc u v, χ r = 1)
    (hgsign : ∀ r ∈ Icc 0 L, χ r ≠ 0 → g r ≤ 0)
    (hgneg : ∀ r ∈ Icc u v, g r < 0) :
    Tendsto (fun t => momentNonlinearPeriod (momentPath b χ c ψ t) g L) (𝓝[<] 1) atBot := by
  have htop := momentDivergence_path_limit hb hχ hψ hg.neg hbpos hδ
    hχbound hdisjoint hcontrol hu huv hv hplateau
    (fun r hr hz => neg_nonneg.mpr (hgsign r hr hz))
    (fun r hr => neg_pos.mpr (hgneg r hr))
  simpa only [Function.comp_def, momentDivergence_period_neg, neg_neg] using
    tendsto_neg_atTop_atBot.comp htop

end
end TightVer401
