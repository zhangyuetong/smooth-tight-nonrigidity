import TightVer401.VisibleConnectorIncomingGinSmoothing

/-! Compact separation and literal full open scalar germs for incoming Gin
gluing.  The modification neighborhood avoids both the ORIGINAL negative
curve and the positive terminal.  These helpers do not assert a smoothing
construction or identify the final gradient inverse with an old inverse. -/
namespace TightVer401
noncomputable section
open Set Function Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

/-- Protect the positive terminal by first removing it from the ambient open
carrier, then use the existing negative-only separation helper for the original
curve.  The terminal is not falsely treated as a negative-height set. -/
theorem visibleConnectorIncomingGinGerm_exists_modification_avoiding_both
    {B : Coord → ℝ} {V C K T : Set Coord} (hV : IsOpen V)
    (hC : IsCompact C) (hK : IsCompact K) (hT : IsCompact T)
    (hCV : C ⊆ V) (hzero : ∀ x ∈ C, B x = 0)
    (hnegative : ∀ x ∈ K, B x < 0) (hpositive : ∀ x ∈ T, 0 < B x) :
    ∃ N : Set Coord, IsOpen N ∧ C ⊆ N ∧ closure N ⊆ V \ (K ∪ T) := by
  have hCT : C ⊆ V \ T := by
    intro x hx
    refine ⟨hCV hx, ?_⟩
    intro hxT
    have hp := hpositive x hxT
    rw [hzero x hx] at hp
    exact lt_irrefl (0 : ℝ) hp
  obtain ⟨N, hN, hCN, hclosure⟩ := visibleConnectorIncomingGin_exists_modification_neighborhood
    (hV.diff hT.isClosed) hC hK hCT hzero hnegative
  refine ⟨N, hN, hCN, ?_⟩
  intro x hx
  have h := hclosure hx
  refine ⟨h.1.1, ?_⟩
  rintro (hxK | hxT)
  · exact h.2 hxK
  · exact h.1.2 hxT

/-- Positive terminal height gives an actual raw scalar germ by continuity,
in addition to the original-negative-curve Gin germ already retained. -/
theorem visibleConnectorIncomingGinGerm_retain_terminal_scalar
    {B Gin raw H : Coord → ℝ} {V N : Set Coord} {T : ℝ → Coord}
    (hV : IsOpen V) (hB : ContinuousOn B V)
    (hTV : ∀ s, T s ∈ V) (hTN : ∀ s, T s ∉ N) (hpos : ∀ s, 0 < B (T s))
    (houtside : ∀ x ∈ V \ N,
      H =ᶠ[𝓝 x] (fun y => if B y < 0 then Gin y else raw y)) :
    ∀ s, H =ᶠ[𝓝 (T s)] raw := by
  intro s
  have hc : ContinuousAt B (T s) := (hB _ (hTV s)).continuousAt (hV.mem_nhds (hTV s))
  have hbranch : (fun y => if B y < 0 then Gin y else raw y) =ᶠ[𝓝 (T s)] raw := by
    filter_upwards [hc.eventually (lt_mem_nhds (hpos s))] with y hy
    exact if_neg (not_lt.mpr hy.le)
  exact (houtside (T s) ⟨hTV s, hTN s⟩).trans hbranch

/-- Pointwise full germs construct an actual OPEN equality neighborhood of
the entire original trace.  No prescribed equality neighborhood is assumed. -/
theorem visibleConnectorIncomingGinGerm_exists_open_equality
    {H f : Coord → ℝ} {V : Set Coord} {p : ℝ → Coord}
    (hV : IsOpen V) (hpV : ∀ s, p s ∈ V) (hgerm : ∀ s, H =ᶠ[𝓝 (p s)] f) :
    ∃ O : Set Coord, IsOpen O ∧ range p ⊆ O ∧ O ⊆ V ∧ EqOn H f O := by
  let O := interior {x | H x = f x} ∩ V
  refine ⟨O, isOpen_interior.inter hV, ?_, inter_subset_right, ?_⟩
  · rintro x ⟨s, rfl⟩
    exact ⟨mem_interior_iff_mem_nhds.mpr (hgerm s), hpV s⟩
  · intro x hx
    exact interior_subset hx.1

/-- Full open branch equality neighborhoods lie inside both the fixed carrier
and the corresponding actual branch domain. -/
theorem visibleConnectorIncomingGinGerm_exists_open_branch_equality
    {H f : Coord → ℝ} {V U : Set Coord} {p : ℝ → Coord}
    (hV : IsOpen V) (hU : IsOpen U) (hpV : ∀ s, p s ∈ V) (hpU : ∀ s, p s ∈ U)
    (hgerm : ∀ s, H =ᶠ[𝓝 (p s)] f) :
    ∃ O : Set Coord, IsOpen O ∧ range p ⊆ O ∧ O ⊆ V ∩ U ∧ EqOn H f O := by
  exact visibleConnectorIncomingGinGerm_exists_open_equality (hV.inter hU)
    (fun s => ⟨hpV s, hpU s⟩) hgerm

end
end TightVer401
