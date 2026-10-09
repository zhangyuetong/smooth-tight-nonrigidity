import TightVer401.ConcaveJetJoinBlendMoments

namespace TightVer401
noncomputable section
open Set MeasureTheory
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_concaveJetJoinBlend_small_radius {c A B ρ η ε : ℝ}
    {hL hR : ℝ → ℝ} {f : ℝ → E} (hρ : 0 < ρ) (hη : 0 < η) (hε : 0 < ε)
    (hleft : A ≤ c - ρ) (hright : c + ρ ≤ B)
    (hfL : ContDiff ℝ ∞ hL) (hfR : ContDiff ℝ ∞ hR) (hf : Continuous f) :
    ∃ r : ℝ, 0 < r ∧ r < ρ ∧ r < ε ∧
      IntervalIntegrable (fun x => concaveJetJoinBlendError c r hL hR x • f x) volume A B ∧
      ‖∫ x in A..B, concaveJetJoinBlendError c r hL hR x • f x‖ < η := by
  obtain ⟨M, hM, hbound⟩ := concaveJetJoinBlend_exists_moment_bound A B hfL.continuous hfR.continuous hf
  have hq : 0 < min ρ (min ε (η / (2 * M + 1))) := by positivity
  obtain ⟨r, hr, hrq⟩ := exists_between hq
  have hall : r < ρ ∧ r < ε ∧ r < η / (2 * M + 1) := by simpa only [lt_min_iff] using hrq
  have hl : A ≤ c - r := by linarith [hall.1]
  have hu : c + r ≤ B := by linarith [hall.1]
  have hn := concaveJetJoinBlendError_integral_norm_le hr hL hR f hl hu (fun x hx =>
    hbound x ⟨hl.trans hx.1, hx.2.trans hu⟩)
  have hηr := (lt_div_iff₀ (show 0 < 2 * M + 1 by positivity)).mp hall.2.2
  refine ⟨r, hr, hall.1, hall.2.1, concaveJetJoinBlendError_intervalIntegrable hfL hfR hf, ?_⟩
  nlinarith [hn]

end
end TightVer401
