import TightVer401.VisibleConnectorOrdinaryFamilyGradientSeparation
import TightVer401.VisibleConnectorTerminalEnclosure

/-! The actual incoming visibility and origin enclosure construct the entire
closed terminal disk inside the SAME incoming gradient fill. -/
namespace TightVer401
noncomputable section
open Set Function Metric OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
open scoped ContDiff Topology

/-- No target nesting premise is needed to place the full closed radius-R
terminal disk inside the retained incoming gradient fill. The caller's positive
Jordan filling is retained, and its origin enclosure comes from D itself. -/
theorem visibleConnectorOrdinaryFamily_closed_terminal_disk_in_incoming
    {Gin : Coord → ℝ} {Uin : Set Coord} {L R : ℝ} [Fact (0 < L)]
    (D : VisibleConnectorIncomingData Gin Uin L R) {H : ℂ ≃ₜ ℂ}
    (hPositive : PositiveJordanParametrization H
      (fun t => seamComplexCoord.symm (D.incoming.gamma (L*t)))) :
    {q : Coord | planarRadius q ≤ R} ⊆ positiveExitInside D.incoming.gamma := by
  have hL : 0 < L := Fact.out
  obtain ⟨hRange, hInside⟩ := visibleConnectorWitnessAssemblyTopology_physical_geometry
    hL hPositive D.incoming.gradient_jordan
  have h0 : (0 : ℂ) ∈ jordanInterior H := by
    have hz := D.incoming.gradient_enclosure
    rw [hInside] at hz
    obtain ⟨z, hz, he⟩ := hz
    have he0 : z = 0 := by
      apply seamComplexCoord.injective
      simpa using he
    simpa only [he0] using hz
  have hFront : ∀ z ∈ frontier (jordanInterior H), R < ‖z‖ := by
    intro z hz
    have hr : seamComplexCoord z ∈ range D.incoming.gamma := by
      rw [hRange]
      exact mem_image_of_mem _ hz
    obtain ⟨s, hs⟩ := hr
    have h := visibleConnectorOrdinaryFamily_incoming_gradient_radius D s
    rw [hs, quadraticRadialFillingRadius_complex] at h
    exact h
  have hDisk := visibleConnector_closedBall_subset_jordanInterior H D.radius_pos.le h0 hFront
  intro q hq
  rw [hInside]
  refine ⟨seamComplexCoord.symm q, hDisk ?_, seamComplexCoord.apply_symm_apply q⟩
  simp only [mem_closedBall, dist_zero_right]
  rw [← quadraticRadialFillingRadius_complex, seamComplexCoord.apply_symm_apply]
  exact hq

/-- In the SAME selected incoming filling, the exact round radius-R filling
is strictly nested; this can feed the final H gradient-chart constructor. -/
theorem visibleConnectorOrdinaryFamily_round_gradient_nesting
    {Gin : Coord → ℝ} {Uin : Set Coord} {L R : ℝ} [Fact (0 < L)]
    (D : VisibleConnectorIncomingData Gin Uin L R) {H : ℂ ≃ₜ ℂ}
    (hPositive : PositiveJordanParametrization H
      (fun t => seamComplexCoord.symm (D.incoming.gamma (L*t)))) :
    closure (jordanInterior (roundDiskChart R D.radius_pos)) ⊆ jordanInterior H := by
  obtain ⟨_, hInside⟩ := visibleConnectorWitnessAssemblyTopology_physical_geometry
    (Fact.out : 0 < L) hPositive D.incoming.gradient_jordan
  have hDisk := visibleConnectorOrdinaryFamily_closed_terminal_disk_in_incoming D hPositive
  rw [roundDiskChart_interior, closure_ball _ D.radius_pos.ne']
  intro z hz
  have hr : planarRadius (seamComplexCoord z) ≤ R := by
    rw [quadraticRadialFillingRadius_complex]
    simpa only [mem_closedBall, dist_zero_right] using hz
  have hi := hDisk hr
  rw [hInside] at hi
  obtain ⟨w, hw, he⟩ := hi
  have heq : w = z := seamComplexCoord.injective he
  simpa only [heq] using hw

end
end TightVer401
