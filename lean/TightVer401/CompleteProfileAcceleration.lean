import TightVer401.MomentControlBump

namespace TightVer401
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

theorem exists_completeProfile_acceleration {H β : ℝ} {F : ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hH : H ∈ U) (hF : ContDiffOn ℝ ∞ F U)
    (hFpos : ∀ z ∈ U, 0 < F z) (hβ : 0 < β) :
    ∃ b : ℝ → ℝ, ContDiff ℝ ∞ b ∧ (∀ z, 0 < b z) ∧
      b =ᶠ[𝓝 H] F ∧ (∀ᶠ z in atTop, b z = β) := by
  obtain ⟨e, he, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hH)
  let χ := momentControlBump H (e / 2) (half_pos he)
  have hχU : tsupport (χ : ℝ → ℝ) ⊆ U := by
    rw [χ.tsupport_eq]
    intro z hz
    apply hball
    have hd : dist z H ≤ e / 2 := hz
    change dist z H < e
    linarith
  let b : ℝ → ℝ := fun z => χ z * F z + (1 - χ z) * β
  have hb : ContDiff ℝ ∞ b := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ U
    · exact (χ.contDiff.contDiffAt.mul (hF.contDiffAt (hU.mem_nhds hz))).add
        ((contDiffAt_const.sub χ.contDiff.contDiffAt).mul contDiffAt_const)
    · have hzχ : z ∉ tsupport (χ : ℝ → ℝ) := fun hs => hz (hχU hs)
      have hzero : (χ : ℝ → ℝ) =ᶠ[𝓝 z] 0 := by
        filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hzχ] with s hs
        exact image_eq_zero_of_notMem_tsupport hs
      apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => β) z).congr_of_eventuallyEq
      filter_upwards [hzero] with s hs
      simp [b, hs]
  refine ⟨b, hb, ?_, ?_, ?_⟩
  · intro z
    by_cases hz : χ z = 0
    · simpa [b, hz] using hβ
    · have hχpos : 0 < χ z := lt_of_le_of_ne χ.nonneg (Ne.symm hz)
      have hzU : z ∈ U := hχU (subset_closure hz)
      have hmain := mul_pos hχpos (hFpos z hzU)
      have hother : 0 ≤ (1 - χ z) * β := mul_nonneg (sub_nonneg.mpr χ.le_one) hβ.le
      dsimp [b]
      linarith
  · filter_upwards [χ.eventuallyEq_one] with z hz
    simp [b, hz]
  · filter_upwards [eventually_ge_atTop (H + e / 2)] with z hz
    have hzero : χ z = 0 := by
      apply χ.zero_of_le_dist
      change e / 2 ≤ dist z H
      rw [Real.dist_eq, abs_of_nonneg (by linarith)]
      linarith
    simp [b, hzero]

end
end TightVer401
