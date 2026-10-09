import TightVer401.VisibleConnectorSourceOrderRound
import TightVer401.VisibleConnectorWitnessAssemblyOrientation
import TightVer401.VisibleConnectorWitnessAssemblyTopology
import TightVer401.VisibleConnectorWitnessAssemblyInputs

/-! Physical source order for the same actual Cartesian map and retained
incoming curve. No scalar construction or global inverse is needed. -/
namespace TightVer401
noncomputable section
open Set Function OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

/-- Positive Cartesian Jacobian on the closed fixed round annulus derives
physical incoming-inside-terminal order from the actual boundary equations. -/
theorem visibleConnectorSourceOrder_physical
    {L : ℝ} (hL : 0 < L) {terminal incoming : ℝ → Coord} {Ho Hi : ℂ ≃ₜ ℂ}
    (hOuter : PositiveJordanParametrization Ho
      (fun t => seamComplexCoord.symm (terminal (L*t))))
    (hInner : PositiveJordanParametrization Hi
      (fun t => seamComplexCoord.symm (incoming (L*t))))
    (hOuterJordan : Schoenflies.IsJordanCurve (positiveExitJordanRange terminal))
    (hInnerJordan : Schoenflies.IsJordanCurve (positiveExitJordanRange incoming))
    {F : Coord → Coord} {O : Set Coord} (hO : IsOpen O) (hF : ContDiffOn ℝ ∞ F O)
    (hKO : {p : Coord | 1 ≤ planarRadius p ∧ planarRadius p ≤ 2} ⊆ O)
    (hJ : ∀ p : Coord, 1 ≤ planarRadius p → planarRadius p ≤ 2 →
      0 < annularJacobian F p)
    (hTerminal : ∀ s, F (saddlePolarChart ![2, 2 * Real.pi * s / L]) = terminal s)
    (hIncoming : ∀ s, F (saddlePolarChart ![1, 2 * Real.pi * s / L]) = incoming s)
    (hDisjoint : Disjoint (range incoming) (range terminal))
    {c : Coord} (hcOuter : c ∈ positiveExitInside terminal)
    (hcInner : c ∈ positiveExitInside incoming) :
    closure (positiveExitInside incoming) ⊆ positiveExitInside terminal := by
  obtain ⟨hRangeOuter,hInsideOuter⟩ :=
    visibleConnectorWitnessAssemblyTopology_physical_geometry hL hOuter hOuterJordan
  obtain ⟨hRangeInner,hInsideInner⟩ :=
    visibleConnectorWitnessAssemblyTopology_physical_geometry hL hInner hInnerJordan
  have hTraceOuter : ∀ t, annularComplexConjugate F (unitCircleParam 0 2 t) =
      seamComplexCoord.symm (terminal (L*t)) := by
    intro t
    exact visibleConnectorWitnessAssembly_complex_physical_boundary
      hL.ne' F 2 terminal hTerminal t
  have hTraceInner : ∀ t, annularComplexConjugate F (unitCircleParam 0 1 t) =
      seamComplexCoord.symm (incoming (L*t)) := by
    intro t
    exact visibleConnectorWitnessAssembly_complex_physical_boundary
      hL.ne' F 1 incoming hIncoming t
  have hDisjoint' : Disjoint (frontier (jordanInterior Ho))
      (frontier (jordanInterior Hi)) := by
    apply Set.disjoint_left.mpr
    intro z hzo hzi
    have hgo : seamComplexCoord z ∈ range terminal := by
      rw [hRangeOuter]
      exact mem_image_of_mem _ hzo
    have hgi : seamComplexCoord z ∈ range incoming := by
      rw [hRangeInner]
      exact mem_image_of_mem _ hzi
    exact Set.disjoint_left.mp hDisjoint hgi hgo
  have hco : seamComplexCoord.symm c ∈ jordanInterior Ho := by
    rw [hInsideOuter] at hcOuter
    obtain ⟨z,hz,hzc⟩ := hcOuter
    rw [← hzc,seamComplexCoord.symm_apply_apply]
    exact hz
  have hci : seamComplexCoord.symm c ∈ jordanInterior Hi := by
    rw [hInsideInner] at hcInner
    obtain ⟨z,hz,hzc⟩ := hcInner
    rw [← hzc,seamComplexCoord.symm_apply_apply]
    exact hz
  have hn := visibleConnectorSourceOrder_round hO hF hKO hJ hOuter hInner
    hTraceOuter hTraceInner hDisjoint' hco hci
  rw [hInsideInner,← seamComplexCoord.image_closure,hInsideOuter]
  rintro q ⟨z,hz,rfl⟩
  exact mem_image_of_mem _ (hn hz)

/-- Derive the canonical ordinary-data source_nesting field for the original
incoming trace and ordinary terminal curve, using their own enclosure facts.
The same caller-selected positive fillings and actual F/O are retained. -/
theorem visibleConnectorSourceOrder_retained_incoming_terminal
    {Gin G : Coord → ℝ} {Uin U : Set Coord} {L R : ℝ} [Fact (0 < L)]
    (D : VisibleConnectorIncomingData Gin Uin L R)
    (T : VisibleConnectorWitnessAssemblyTerminalFacts G U L) {Ho Hi : ℂ ≃ₜ ℂ}
    (hOuter : PositiveJordanParametrization Ho
      (fun t => seamComplexCoord.symm (T.p (L*t))))
    (hInner : PositiveJordanParametrization Hi
      (fun t => seamComplexCoord.symm (D.incoming.p (L*t))))
    {F : Coord → Coord} {O : Set Coord} (hO : IsOpen O) (hF : ContDiffOn ℝ ∞ F O)
    (hKO : {p : Coord | 1 ≤ planarRadius p ∧ planarRadius p ≤ 2} ⊆ O)
    (hJ : ∀ p : Coord, 1 ≤ planarRadius p → planarRadius p ≤ 2 →
      0 < annularJacobian F p)
    (hTerminal : ∀ s, F (saddlePolarChart ![2, 2 * Real.pi * s / L]) = T.p s)
    (hIncoming : ∀ s, F (saddlePolarChart ![1, 2 * Real.pi * s / L]) = D.incoming.p s)
    (hDisjoint : Disjoint (range D.incoming.p) (range T.p)) :
    closure (positiveExitInside D.incoming.p) ⊆ positiveExitInside T.p := by
  exact visibleConnectorSourceOrder_physical (Fact.out : 0 < L) hOuter hInner
    T.source_jordan D.incoming.source_jordan hO hF hKO hJ hTerminal hIncoming
    hDisjoint T.source_enclosure D.incoming.source_enclosure

end
end TightVer401
