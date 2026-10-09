import TightVer401.ConcaveJetJoinBlend
import Mathlib.Topology.MetricSpace.Pseudo.Defs

namespace TightVer401
noncomputable section
open Set
open scoped ContDiff Topology

 theorem exists_revolutionEnd_positive_extension {q : ℝ → ℝ} {H : ℝ}
    (hq : ContDiff ℝ ∞ q) (hpos : ∀ z ∈ Ici H, 0 < q z) :
    ∃ Q : ℝ → ℝ, ContDiff ℝ ∞ Q ∧ (∀ z, 0 < Q z) ∧
      ∃ b < H, EqOn Q q (Ioi b) := by
  have hH : 0 < q H := hpos H (by simp)
  obtain ⟨δ, hδ, hb⟩ := Metric.mem_nhds_iff.mp
    ((isOpen_lt continuous_const hq.continuous).mem_nhds hH)
  let a := H - δ / 2
  let b := H - δ / 4
  let c := (a+b) / 2
  let r := (b-a) / 2
  have hab : a < b := by dsimp [a, b]; linarith
  have hr : 0 < r := div_pos (sub_pos.mpr hab) (by norm_num)
  have hcL : c-r = a := by dsimp [c, r]; ring
  have hcR : c+r = b := by dsimp [c, r]; ring
  have hpositive : ∀ z, a < z → 0 < q z := by
    intro z hz
    by_cases hzH : H ≤ z
    · exact hpos z hzH
    · have hzH' : z < H := lt_of_not_ge hzH
      apply hb
      rw [Metric.mem_ball, Real.dist_eq, abs_of_neg (sub_neg.mpr hzH')]
      dsimp [a] at hz
      linarith
  let Q := concaveJetJoinBlendAcceleration c r (fun _ => q H) q
  refine ⟨Q, concaveJetJoinBlendAcceleration_contDiff contDiff_const hq, ?_, b, ?_, ?_⟩
  · intro z
    by_cases hz : z ≤ a
    · change 0 < concaveJetJoinBlendAcceleration c r (fun _ => q H) q z
      rw [concaveJetJoinBlendAcceleration_left hr _ _ (by rwa [hcL])]
      exact hH
    · have hzq := hpositive z (lt_of_not_ge hz)
      exact concaveJetJoinBlendAcceleration_pos (lt_min hH hzq)
        (min_le_left _ _) (min_le_right _ _)
  · dsimp [b]; linarith
  · intro z hz
    exact concaveJetJoinBlendAcceleration_right hr _ _ (by rw [hcR]; exact hz.le)

end
end TightVer401
