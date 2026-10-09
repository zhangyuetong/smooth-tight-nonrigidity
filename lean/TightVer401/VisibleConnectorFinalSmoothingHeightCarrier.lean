import TightVer401.VisibleConnectorFinalSmoothingHeight
import TightVer401.VisibleConnectorFinalSmoothingCarrier

/-! Concrete SAME-inverse height coverage of the full rebased band and its
zero seam. Compactness refers to the literal original lower trace and terminal
trace, not the intermediate displaced seam. No smoothing result is assumed. -/
namespace TightVer401
noncomputable section
open Set Function OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

/-- Literal height supplies carrier coverage for EVERY closed rebased ruling. -/
theorem visibleConnectorFinalSmoothingHeightCarrier_closed_band
    {L : ℝ} (hL : 0 < L) {pc wc : ℝ → Coord} {a b d : ℝ → ℝ}
    (hpL : Periodic (visibleConnectorRebasedSource pc wc a b) L)
    (hwL : Periodic (visibleConnectorRebasedRuling wc a d) L)
    (hbL : Periodic b L) (hdL : Periodic d L) (hd : ∀ s, 0 < d s)
    (E : OpenPartialHomeomorph Coord Coord)
    (hE : (E : Coord → Coord) = visibleConnectorCartesianSource L
      (visibleConnectorRebasedSource pc wc a b) (visibleConnectorRebasedRuling wc a d)
      (fun _ => 1))
    (hclosed : {z | 1 ≤ planarRadius z ∧ planarRadius z ≤ 2} ⊆ E.source)
    {Vraw GinU : Set Coord}
    (hRaw : ∀ s u : ℝ, u ∈ Icc (0 : ℝ) 1 →
      visibleConnectorSource (visibleConnectorRebasedSource pc wc a b)
        (visibleConnectorRebasedRuling wc a d) (![s, u] : Coord) ∈ Vraw)
    (hGin : ∀ s t : ℝ, b s ≤ t → t ≤ 0 →
      visibleConnectorSource pc wc (![a s, t] : Coord) ∈ GinU) :
    visibleConnectorFinalSmoothingClosedRebasedBand pc wc a b d ⊆
      visibleConnectorFinalSmoothingCarrier Vraw GinU
        (visibleConnectorFinalSmoothingHeight L b d E) := by
  rintro x ⟨s, u, hu, rfl⟩
  have hheight := (visibleConnectorFinalSmoothingHeight_closed_band hL hpL hwL hbL hdL
    E hE hclosed s u hu.1 hu.2).2
  refine ⟨hRaw s u hu, ?_⟩
  by_cases hpos : 0 < b s + u * d s
  · right
    change 0 < visibleConnectorFinalSmoothingHeight L b d E _
    rw [hheight]
    exact hpos
  · left
    rw [visibleConnector_rebase_source]
    have hlo : b s ≤ b s + u * d s := by
      have hmul := mul_nonneg hu.1 (hd s).le
      linarith
    exact hGin s (b s + u * d s) hlo (le_of_not_gt hpos)

/-- The actual displaced zero seam lies in the full carrier, by its explicit
interior ruling parameter -b/d. -/
theorem visibleConnectorFinalSmoothingHeightCarrier_seam
    {L : ℝ} (hL : 0 < L) {pc wc : ℝ → Coord} {a b d : ℝ → ℝ}
    (hpL : Periodic (visibleConnectorRebasedSource pc wc a b) L)
    (hwL : Periodic (visibleConnectorRebasedRuling wc a d) L)
    (hbL : Periodic b L) (hdL : Periodic d L) (hd : ∀ s, 0 < d s)
    (E : OpenPartialHomeomorph Coord Coord)
    (hE : (E : Coord → Coord) = visibleConnectorCartesianSource L
      (visibleConnectorRebasedSource pc wc a b) (visibleConnectorRebasedRuling wc a d)
      (fun _ => 1))
    (hclosed : {z | 1 ≤ planarRadius z ∧ planarRadius z ≤ 2} ⊆ E.source)
    {Vraw GinU : Set Coord}
    (hRaw : ∀ s u : ℝ, u ∈ Icc (0 : ℝ) 1 →
      visibleConnectorSource (visibleConnectorRebasedSource pc wc a b)
        (visibleConnectorRebasedRuling wc a d) (![s, u] : Coord) ∈ Vraw)
    (hGin : ∀ s t : ℝ, b s ≤ t → t ≤ 0 →
      visibleConnectorSource pc wc (![a s, t] : Coord) ∈ GinU)
    (hbneg : ∀ s, b s < 0) (htpos : ∀ s, 0 < b s + d s) (s : ℝ) :
    pc (a s) ∈ visibleConnectorFinalSmoothingCarrier Vraw GinU
      (visibleConnectorFinalSmoothingHeight L b d E) := by
  have hu0 : 0 < -b s / d s := div_pos (neg_pos.mpr (hbneg s)) (hd s)
  have hu1 : -b s / d s < 1 := (div_lt_one (hd s)).mpr (by linarith [htpos s])
  have hz : b s + (-b s / d s) * d s = 0 := by
    field_simp [(hd s).ne']
    <;> ring
  have hBand : visibleConnectorSource (visibleConnectorRebasedSource pc wc a b)
      (visibleConnectorRebasedRuling wc a d) (![s, -b s / d s] : Coord) ∈
      visibleConnectorFinalSmoothingClosedRebasedBand pc wc a b d :=
    ⟨s, -b s / d s, ⟨hu0.le, hu1.le⟩, rfl⟩
  have hmem := visibleConnectorFinalSmoothingHeightCarrier_closed_band hL hpL hwL hbL hdL
    hd E hE hclosed hRaw hGin hBand
  rw [visibleConnector_rebase_source, hz] at hmem
  simpa only [visibleConnectorSource, Matrix.cons_val_zero, Matrix.cons_val_one,
    zero_smul, add_zero] using hmem

private theorem visibleConnectorFinalSmoothing_periodic_range_compact
    {L : ℝ} (hL : 0 < L) {f : ℝ → Coord}
    (hf : Continuous f) (hp : Periodic f L) : IsCompact (range f) := by
  have heq : f '' Icc (0 : ℝ) L = range f := by
    apply Subset.antisymm (image_subset_range _ _)
    rintro x ⟨s, rfl⟩
    refine ⟨toIcoMod hL 0 s, Ico_subset_Icc_self (toIcoMod_mem_Ico' hL s), ?_⟩
    exact (seam_periodic_eq_representative hL hp s).symm
  rw [← heq]
  exact isCompact_Icc.image hf

/-- Compactness of the literal lower/original and upper/terminal boundaries. -/
theorem visibleConnectorFinalSmoothingHeightCarrier_boundary_compact
    {L : ℝ} (hL : 0 < L) {pc wc : ℝ → Coord} {a b d : ℝ → ℝ}
    (hp : ContDiff ℝ ∞ pc) (hw : ContDiff ℝ ∞ wc) (ha : ContDiff ℝ ∞ a)
    (hb : ContDiff ℝ ∞ b) (hd : ContDiff ℝ ∞ d)
    (hpL : Periodic (visibleConnectorRebasedSource pc wc a b) L)
    (hwL : Periodic (visibleConnectorRebasedRuling wc a d) L) :
    IsCompact (range (visibleConnectorRebasedSource pc wc a b)) ∧
      IsCompact (range (fun s => visibleConnectorRebasedSource pc wc a b s +
        visibleConnectorRebasedRuling wc a d s)) := by
  have hpSmooth : ContDiff ℝ ∞ (visibleConnectorRebasedSource pc wc a b) :=
    (hp.comp ha).add (hb.smul (hw.comp ha))
  have hwSmooth : ContDiff ℝ ∞ (visibleConnectorRebasedRuling wc a d) :=
    hd.smul (hw.comp ha)
  have htPeriod : Periodic (fun s => visibleConnectorRebasedSource pc wc a b s +
      visibleConnectorRebasedRuling wc a d s) L := by
    intro s
    change visibleConnectorRebasedSource pc wc a b (s + L) +
      visibleConnectorRebasedRuling wc a d (s + L) =
      visibleConnectorRebasedSource pc wc a b s + visibleConnectorRebasedRuling wc a d s
    rw [hpL s, hwL s]
  exact ⟨visibleConnectorFinalSmoothing_periodic_range_compact hL hpSmooth.continuous hpL,
    visibleConnectorFinalSmoothing_periodic_range_compact hL
      (hpSmooth.add hwSmooth).continuous htPeriod⟩

end
end TightVer401

