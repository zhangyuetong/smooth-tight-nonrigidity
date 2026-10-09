import TightVer401.CorrugatedRootLimits

namespace TightVer401
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

theorem corrugatedRoot_exists_unique {ε : ℝ} (hε : |ε| < 1) :
    ∃! k : ℝ, corrugatedRootIntegral ε k = 0 := by
  have hc : Continuous (corrugatedCosExpectation ε) :=
    continuous_iff_continuousAt.mpr (fun k => (corrugatedCosExpectation_hasDerivAt hε k).continuousAt)
  have hleft : ∀ᶠ k in atBot, (-1 / 2 : ℝ) < corrugatedCosExpectation ε k :=
    corrugatedCosExpectation_tendsto_atBot hε |>.eventually (lt_mem_nhds (by norm_num))
  obtain ⟨a, ha⟩ := hleft.exists
  have hright : ∀ᶠ k in atTop, corrugatedCosExpectation ε k < (-1 / 2 : ℝ) :=
    corrugatedCosExpectation_tendsto_atTop hε |>.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨b, hb, hab⟩ := (hright.and (eventually_ge_atTop a)).exists
  obtain ⟨k, _, hk⟩ := intermediate_value_Icc' hab hc.continuousOn ⟨hb.le, ha.le⟩
  have hroot := (corrugatedRootIntegral_zero_iff hε k).mpr hk
  exact ⟨k, hroot, fun y hy => corrugatedRootIntegral_unique hε hy hroot⟩

def corrugatedRoot (ε : ℝ) (hε : |ε| < 1) : ℝ :=
  Classical.choose (corrugatedRoot_exists_unique hε).exists

theorem corrugatedRoot_spec (ε : ℝ) (hε : |ε| < 1) :
    corrugatedRootIntegral ε (corrugatedRoot ε hε) = 0 :=
  Classical.choose_spec (corrugatedRoot_exists_unique hε).exists

theorem corrugatedRoot_eq_iff (ε : ℝ) (hε : |ε| < 1) (k : ℝ) :
    corrugatedRootIntegral ε k = 0 ↔ k = corrugatedRoot ε hε := by
  constructor
  · intro hk
    exact corrugatedRootIntegral_unique hε hk (corrugatedRoot_spec ε hε)
  · rintro rfl
    exact corrugatedRoot_spec ε hε

theorem corrugatedRoot_exists_unique_nat {N : ℕ} (hN : 10000 ≤ N) :
    ∃! k : ℝ, (∫ x in 0..(2 * Real.pi), Real.exp (-k * Real.cos x) *
      (1 + (1 / (N : ℝ)) * Real.sin x) ^ 2 * (1 + 2 * Real.cos x)) = 0 := by
  have hNreal : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hε : |1 / (N : ℝ)| < 1 := by
    rw [abs_of_pos (div_pos zero_lt_one (zero_lt_one.trans hNreal))]
    exact (div_lt_one (zero_lt_one.trans hNreal)).mpr hNreal
  simpa only [corrugatedRootIntegral, corrugatedWeight] using corrugatedRoot_exists_unique hε

end
end TightVer401
