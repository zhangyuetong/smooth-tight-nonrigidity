import TightVer401.VisibleConnectorSourceOrderPhysical
import TightVer401.VisibleConnectorTerminalJordan

/-! Physical source closure from the SAME constructed raw source inverse.
Its two round boundary circles are disjoint by inverse injectivity. Signed
order then produces nesting, and the retained fillings identify the exact
physical closed annulus and its raw-U coverage. -/
namespace TightVer401
noncomputable section
open Set Function OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

/-- Consume actual raw source fields and ordinary terminal det/turn facts.
No separate source-boundary disjointness, source nesting or new filling is
assumed. This is source geometry only; the final H inverse is separate. -/
theorem visibleConnectorOrdinaryFamilySourceClosure_actual
    {L : ℝ} (hL : 0 < L) {incoming terminal : ℝ → Coord}
    {Ho Hi : ℂ ≃ₜ ℂ} {F : Coord → Coord} {Uraw : Set Coord}
    (E : OpenPartialHomeomorph Coord Coord) (hE : (E : Coord → Coord) = F)
    (hF : ContDiffOn ℝ ∞ F E.source)
    (hK : {z : Coord | 1 ≤ planarRadius z ∧ planarRadius z ≤ 2} ⊆ E.source)
    (hJac : ∀ z ∈ E.source, 0 < annularJacobian F z)
    (hIncoming : ∀ s, F (saddlePolarChart ![1, 2 * Real.pi * s / L]) = incoming s)
    (hTerminal : ∀ s, F (saddlePolarChart ![2, 2 * Real.pi * s / L]) = terminal s)
    (hInner : PositiveJordanParametrization Hi
      (fun t => seamComplexCoord.symm (incoming (L * t))))
    (hOuter : PositiveJordanParametrization Ho
      (fun t => seamComplexCoord.symm (terminal (L * t))))
    (hIncomingJordan : Schoenflies.IsJordanCurve (positiveExitJordanRange incoming))
    (hT : ContDiff ℝ ∞ terminal) (hTL : Periodic terminal L)
    (hTNonzero : ∀ s, positiveExitComplexTrace terminal s ≠ 0)
    (hTTurn : HasPositiveArgumentTurn (positiveExitComplexTrace terminal) L)
    (hTDet : ∀ s, 0 < visibleConnectorDet (terminal s) (deriv terminal s))
    (hcInner : (0 : ℂ) ∈ jordanInterior Hi) (hcOuter : (0 : ℂ) ∈ jordanInterior Ho)
    (hBandU : annularCoordJordanClosure Ho Hi ⊆ Uraw) :
    Schoenflies.IsJordanCurve (positiveExitJordanRange terminal) ∧
    Disjoint (range incoming) (range terminal) ∧
    positiveExitInside incoming = seamComplexCoord '' jordanInterior Hi ∧
    positiveExitInside terminal = seamComplexCoord '' jordanInterior Ho ∧
    closure (positiveExitInside incoming) ⊆ positiveExitInside terminal ∧
    closure (positiveExitInside terminal \ closure (positiveExitInside incoming)) =
      annularCoordJordanClosure Ho Hi ∧
    closure (positiveExitInside terminal \ closure (positiveExitInside incoming)) ⊆ Uraw := by
  have hTerminalJordan : Schoenflies.IsJordanCurve (positiveExitJordanRange terminal) :=
    (visibleConnector_positive_det_turn_jordan hL hT hTL hTNonzero hTTurn hTDet).2
  have hR1 (s : ℝ) : planarRadius (saddlePolarChart ![1, 2 * Real.pi * s / L]) = 1 :=
    angularDescent_radius_polar (q := ![1, 2 * Real.pi * s / L]) (by norm_num)
  have hR2 (s : ℝ) : planarRadius (saddlePolarChart ![2, 2 * Real.pi * s / L]) = 2 :=
    angularDescent_radius_polar (q := ![2, 2 * Real.pi * s / L]) (by norm_num)
  have hDisjoint : Disjoint (range incoming) (range terminal) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨s, rfl⟩ ⟨t, ht⟩
    have hOne : saddlePolarChart ![1, 2 * Real.pi * s / L] ∈ E.source :=
      hK (by rw [mem_setOf_eq, hR1]; norm_num)
    have hTwo : saddlePolarChart ![2, 2 * Real.pi * t / L] ∈ E.source :=
      hK (by rw [mem_setOf_eq, hR2]; norm_num)
    have heq : E (saddlePolarChart ![1, 2 * Real.pi * s / L]) =
        E (saddlePolarChart ![2, 2 * Real.pi * t / L]) := by
      rw [hE, hIncoming, hTerminal, ht]
    have hsource := E.injOn hOne hTwo heq
    have hrad := congrArg planarRadius hsource
    rw [hR1, hR2] at hrad
    norm_num at hrad
  obtain ⟨_hIncomingRange, hInsideInner⟩ :=
    visibleConnectorWitnessAssemblyTopology_physical_geometry hL hInner hIncomingJordan
  obtain ⟨_hTerminalRange, hInsideOuter⟩ :=
    visibleConnectorWitnessAssemblyTopology_physical_geometry hL hOuter hTerminalJordan
  have hInner0 : (0 : Coord) ∈ positiveExitInside incoming := by
    rw [hInsideInner]
    exact ⟨0, hcInner, by simp⟩
  have hOuter0 : (0 : Coord) ∈ positiveExitInside terminal := by
    rw [hInsideOuter]
    exact ⟨0, hcOuter, by simp⟩
  have hNested := visibleConnectorSourceOrder_physical hL hOuter hInner
    hTerminalJordan hIncomingJordan E.open_source hF hK
    (fun z hz1 hz2 => hJac z (hK ⟨hz1, hz2⟩))
    hTerminal hIncoming hDisjoint hOuter0 hInner0
  obtain ⟨_hComplexNested, _hAnnulus, _hOpen, _hCompact, hClosure, _hFrontier, _hSeparate⟩ :=
    visibleConnectorWitnessAssemblyTopology_annulus_geometry hL hOuter hInner
      hTerminalJordan hIncomingJordan hNested
  refine ⟨hTerminalJordan, hDisjoint, hInsideInner, hInsideOuter, hNested, hClosure, ?_⟩
  rw [hClosure]
  exact hBandU

end
end TightVer401
