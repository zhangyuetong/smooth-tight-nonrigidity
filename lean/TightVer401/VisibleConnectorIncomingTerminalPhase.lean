import TightVer401.VisibleConnectorIncomingTerminalRebase

/-! Preserve the ONE previously chosen terminal filling under the literal
phase rebase. The retained degree-one phase shift constructs surjectivity by
the intermediate value theorem, so range equality is proved rather than an
extra terminal identification premise. -/
namespace TightVer401
noncomputable section
open Set Function OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- An actual continuous degree-one lift is surjective on the physical line. -/
theorem visibleConnectorIncomingTerminal_phase_surjective
    {L : ℝ} (hL : 0 < L) {a : ℝ → ℝ} (ha : Continuous a)
    (hshift : ∀ s, a (s + L) = a s + L) : Surjective a := by
  have hper : Periodic (fun s => a s - s) L := by
    intro s
    dsimp only
    rw [hshift s]
    ring
  intro y
  obtain ⟨n, hn, _⟩ := existsUnique_sub_zsmul_mem_Ico hL y (a 0)
  have hn' : y - n • L ∈ Icc (a 0) (a L) := by
    have he : a L = a 0 + L := by simpa only [zero_add] using hshift 0
    rw [he]
    exact ⟨hn.1, hn.2.le⟩
  obtain ⟨s, hs, he⟩ := intermediate_value_Icc hL.le ha.continuousOn hn'
  refine ⟨s + n • L, ?_⟩
  have hp := hper.zsmul n s
  change a (s + n • L) - (s + n • L) = a s - s at hp
  linarith

/-- Rebased terminal and original terminal have exactly the same range, so
all downstream source/frontier and filled-disk statements retain SAME H. -/
theorem visibleConnectorIncomingTerminal_rebase_range_eq
    {L : ℝ} (hL : 0 < L) (p w : ℝ → Coord) {a b d tc : ℝ → ℝ}
    (ha : Continuous a) (hshift : ∀ s, a (s + L) = a s + L)
    (hd : ∀ s, d s = tc (a s) - b s) :
    range (fun s => positiveExitComplexPoint
      (visibleConnectorSource (visibleConnectorRebasedSource p w a b)
        (visibleConnectorRebasedRuling w a d) (![s, 1] : Coord))) =
    range (fun s => positiveExitComplexPoint
      (visibleConnectorSource p w (![s, tc s] : Coord))) := by
  apply Subset.antisymm
  · rintro z ⟨s, rfl⟩
    refine ⟨a s, ?_⟩
    dsimp only
    rw [visibleConnectorIncomingTerminal_rebase_eq p w a b d tc hd s]
  · rintro z ⟨s, rfl⟩
    obtain ⟨t, ht⟩ := visibleConnectorIncomingTerminal_phase_surjective hL ha hshift s
    refine ⟨t, ?_⟩
    dsimp only
    rw [visibleConnectorIncomingTerminal_rebase_eq p w a b d tc hd t, ht]

/-- A previously chosen filling has the SAME actual rebased terminal frontier.
This transfers an identity, without making a second existential filling choice. -/
theorem visibleConnectorIncomingTerminal_rebase_frontier
    {L : ℝ} (hL : 0 < L) (p w : ℝ → Coord) {a b d tc : ℝ → ℝ}
    (ha : Continuous a) (hshift : ∀ s, a (s + L) = a s + L)
    (hd : ∀ s, d s = tc (a s) - b s) (H : ℂ ≃ₜ ℂ)
    (hfront : range (fun s => positiveExitComplexPoint
      (visibleConnectorSource p w (![s, tc s] : Coord))) = frontier (jordanInterior H)) :
    range (fun s => positiveExitComplexPoint
      (visibleConnectorSource (visibleConnectorRebasedSource p w a b)
        (visibleConnectorRebasedRuling w a d) (![s, 1] : Coord))) = frontier (jordanInterior H) := by
  rw [visibleConnectorIncomingTerminal_rebase_range_eq hL p w ha hshift hd]
  exact hfront

end
end TightVer401

