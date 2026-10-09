import TightVer401.ProfileCutoffSupport

namespace TightVer401
noncomputable section
open Set

theorem exists_band_cutoff {A : Type*} [TopologicalSpace A] [CompactSpace A] [Nonempty A]
    {ρ W : A → ℝ} {b : ℝ} (hρ : Continuous ρ) (hW : Continuous W)
    (hρpos : ∀ a, 0 < ρ a) (hb : 0 < b) :
    ∃ cb : ℝ, (∀ a, 1 / (ρ a * b) - W a ≤ cb) ∧
      ∃ a, 1 / (ρ a * b) - W a = cb := by
  have hc : Continuous (fun a => 1 / (ρ a * b) - W a) :=
    (continuous_const.div (hρ.mul continuous_const)
      (fun a => mul_ne_zero (ne_of_gt (hρpos a)) (ne_of_gt hb))).sub hW
  obtain ⟨a, _, ha⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hc.continuousOn
  exact ⟨1 / (ρ a * b) - W a, fun x => ha (mem_univ x), a, rfl⟩

theorem profile_support_above_attained_cutoff {A : Type*} {ρ W : A → ℝ} {F : ℝ → ℝ}
    {b cb : ℝ} (hattained : ∃ a, 1 / (ρ a * b) - W a = cb)
    (hsupport : ∀ a, ∀ c ∈ tsupport F, 1 / (ρ a * b) - W a < c) :
    tsupport F ⊆ Ioi cb := by
  obtain ⟨a, ha⟩ := hattained
  intro c hc
  change cb < c
  rw [← ha]
  exact hsupport a c hc

theorem support_above_cutoff_iff_pointwise {A : Type*} {ρ W : A → ℝ} {F : ℝ → ℝ}
    {b cb : ℝ} (hmax : ∀ a, 1 / (ρ a * b) - W a ≤ cb)
    (hattained : ∃ a, 1 / (ρ a * b) - W a = cb) :
    tsupport F ⊆ Ioi cb ↔ ∀ a, ∀ c ∈ tsupport F, 1 / (ρ a * b) - W a < c := by
  constructor
  · intro h a c hc
    exact (hmax a).trans_lt (h hc)
  · exact profile_support_above_attained_cutoff hattained

end
end TightVer401
