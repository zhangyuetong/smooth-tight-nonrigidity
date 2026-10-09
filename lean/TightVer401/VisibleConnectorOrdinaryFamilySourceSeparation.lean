import TightVer401.VisibleConnectorOrdinaryFamilyGradientSeparation
import TightVer401.VisibleConnectorWitnessAssemblyInputs

/-! Boundary separation for the SAME final potential. The full incoming open
 germ identifies its incoming gradient, and the literal terminal circle gives
 gradient separation. Evaluating this one gradient then separates the sources. -/
namespace TightVer401
noncomputable section
open Set Function OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

/-- The actual full-turn radius-R terminal gradient is disjoint from the SAME
incoming gradient, using only ordinary visibility and its circle equation. -/
theorem visibleConnectorOrdinaryFamily_terminal_circle_gradient_disjoint
    {Gin : Coord → ℝ} {Uin : Set Coord} {L R : ℝ} [Fact (0 < L)]
    (D : VisibleConnectorIncomingData Gin Uin L R)
    {gamma : ℝ → Coord} {theta : ℝ → ℝ}
    (hTheta : Continuous theta)
    (hShift : ∀ s, theta (s + L) = theta s + 2 * Real.pi)
    (hCircle : ∀ s, gamma s = R • visibleConnectorUnitDirection (theta s)) :
    Disjoint (range D.incoming.gamma) (range gamma) := by
  have hRange : range gamma = {y : Coord | planarRadius y = R} := by
    have hfun : gamma = fun s => R • visibleConnectorUnitDirection (theta s) :=
      funext hCircle
    rw [hfun]
    exact visibleConnectorWitnessAssembly_terminal_circle_range D.radius_pos hTheta hShift
  apply visibleConnectorOrdinaryFamily_gradient_boundaries_disjoint D
  intro s
  have hs : gamma s ∈ {y : Coord | planarRadius y = R} := by
    rw [← hRange]
    exact mem_range_self s
  exact hs

/-- Source boundary separation follows by evaluating the SAME final gradient.
No source inverse, source nesting, or injectivity of the gradient is assumed. -/
theorem visibleConnectorOrdinaryFamily_source_boundaries_disjoint
    {Gin G : Coord → ℝ} {Uin U N : Set Coord} {L R : ℝ} [Fact (0 < L)]
    (D : VisibleConnectorIncomingData Gin Uin L R)
    (T : VisibleConnectorWitnessAssemblyTerminalFacts G U L)
    (hN : IsOpen N) (hpN : range D.incoming.p ⊆ N) (hGerm : EqOn G Gin N)
    (hCircle : ∀ s, planarRadius (T.gamma s) = R) :
    Disjoint (range D.incoming.p) (range T.p) := by
  obtain ⟨hIncoming, _⟩ := visibleConnectorWitnessAssembly_incoming_germ D hN hpN hGerm
  have hDisjoint := visibleConnectorOrdinaryFamily_gradient_boundaries_disjoint D hCircle
  apply disjoint_left.mpr
  rintro q ⟨s, rfl⟩ ⟨t, ht⟩
  have hTerminal : planarGradient G (T.p t) = T.gamma t := by
    rw [T.actual_gradient]
    rfl
  have he : T.gamma t = D.incoming.gamma s := by
    rw [← hTerminal, ht, (hIncoming s).2]
  exact disjoint_left.mp hDisjoint (mem_range_self s) ⟨t, he⟩

end
end TightVer401
