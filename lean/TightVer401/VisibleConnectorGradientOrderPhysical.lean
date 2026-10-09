import TightVer401.VisibleConnectorGradientOrderApplication
import TightVer401.VisibleConnectorWitnessAssemblyTopology

/-! Physical-period consumer of the same supplied final gradient order.
Only the existing coordinate/Inside bridges are applied; no new degree or
Jordan nesting construction is introduced. -/
namespace TightVer401
noncomputable section
open Set Function OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

/-- Derive the canonical physical reverse gradient nesting from actual final
scalar data, ordinary source nesting, disjoint gradient boundaries and a
common enclosed point. The original physical period and traces are retained. -/
theorem visibleConnectorGradientOrder_physical
    {L : ℝ} (hL : 0 < L)
    {pOuter pInner gammaOuter gammaInner : ℝ → Coord} {Ho Hi To Ti : ℂ ≃ₜ ℂ}
    (hSourceOuter : PositiveJordanParametrization Ho
      (fun t => seamComplexCoord.symm (pOuter (L*t))))
    (hSourceInner : PositiveJordanParametrization Hi
      (fun t => seamComplexCoord.symm (pInner (L*t))))
    (hTargetInner : PositiveJordanParametrization Ti
      (fun t => seamComplexCoord.symm (gammaOuter (L*t))))
    (hTargetOuter : PositiveJordanParametrization To
      (fun t => seamComplexCoord.symm (gammaInner (L*t))))
    (hSourceOuterJordan : Schoenflies.IsJordanCurve (positiveExitJordanRange pOuter))
    (hSourceInnerJordan : Schoenflies.IsJordanCurve (positiveExitJordanRange pInner))
    (hTargetInnerJordan : Schoenflies.IsJordanCurve (positiveExitJordanRange gammaOuter))
    (hTargetOuterJordan : Schoenflies.IsJordanCurve (positiveExitJordanRange gammaInner))
    (hSourceNested : closure (positiveExitInside pInner) ⊆ positiveExitInside pOuter)
    {G : Coord → ℝ} {U : Set Coord} (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U)
    (hKU : closure (positiveExitInside pOuter \ closure (positiveExitInside pInner)) ⊆ U)
    (hNeg : ∀ q ∈ positiveExitInside pOuter \ closure (positiveExitInside pInner),
      (planarHessian G q).det < 0)
    (hTraceOuter : ∀ s, planarGradient G (pOuter s) = gammaOuter s)
    (hTraceInner : ∀ s, planarGradient G (pInner s) = gammaInner s)
    (hDisjoint : Disjoint (range gammaOuter) (range gammaInner))
    {c : Coord} (hcInner : c ∈ positiveExitInside gammaOuter)
    (hcOuter : c ∈ positiveExitInside gammaInner) :
    closure (positiveExitInside gammaOuter) ⊆ positiveExitInside gammaInner := by
  obtain ⟨hnS,hAnnS,_hOpenS,_hCompactS,hClosedS,_hFrontS,_hDisjointS⟩ :=
    visibleConnectorWitnessAssemblyTopology_annulus_geometry hL hSourceOuter hSourceInner
      hSourceOuterJordan hSourceInnerJordan hSourceNested
  obtain ⟨hRangeInner,hInsideInner⟩ :=
    visibleConnectorWitnessAssemblyTopology_physical_geometry hL hTargetInner hTargetInnerJordan
  obtain ⟨hRangeOuter,hInsideOuter⟩ :=
    visibleConnectorWitnessAssemblyTopology_physical_geometry hL hTargetOuter hTargetOuterJordan
  have hKU' : annularCoordJordanClosure Ho Hi ⊆ U := by
    rw [← hClosedS]
    exact hKU
  have hNeg' : ∀ q ∈ annularCoordJordanInterior Ho Hi, (planarHessian G q).det < 0 := by
    rw [← hAnnS]
    exact hNeg
  have hTraceOuter' : ∀ t,
      annularComplexConjugate (planarGradient G) (seamComplexCoord.symm (pOuter (L*t))) =
        seamComplexCoord.symm (gammaOuter (L*t)) := by
    intro t
    change seamComplexCoord.symm (planarGradient G
      (seamComplexCoord (seamComplexCoord.symm (pOuter (L*t))))) = _
    rw [seamComplexCoord.apply_symm_apply,hTraceOuter]
  have hTraceInner' : ∀ t,
      annularComplexConjugate (planarGradient G) (seamComplexCoord.symm (pInner (L*t))) =
        seamComplexCoord.symm (gammaInner (L*t)) := by
    intro t
    change seamComplexCoord.symm (planarGradient G
      (seamComplexCoord (seamComplexCoord.symm (pInner (L*t))))) = _
    rw [seamComplexCoord.apply_symm_apply,hTraceInner]
  have hDisjoint' : Disjoint (frontier (jordanInterior Ti)) (frontier (jordanInterior To)) := by
    apply Set.disjoint_left.mpr
    intro z hzi hzo
    have hgi : seamComplexCoord z ∈ range gammaOuter := by
      rw [hRangeInner]
      exact mem_image_of_mem _ hzi
    have hgo : seamComplexCoord z ∈ range gammaInner := by
      rw [hRangeOuter]
      exact mem_image_of_mem _ hzo
    exact Set.disjoint_left.mp hDisjoint hgi hgo
  have hci : seamComplexCoord.symm c ∈ jordanInterior Ti := by
    rw [hInsideInner] at hcInner
    obtain ⟨z,hz,hzc⟩ := hcInner
    rw [← hzc,seamComplexCoord.symm_apply_apply]
    exact hz
  have hco : seamComplexCoord.symm c ∈ jordanInterior To := by
    rw [hInsideOuter] at hcOuter
    obtain ⟨z,hz,hzc⟩ := hcOuter
    rw [← hzc,seamComplexCoord.symm_apply_apply]
    exact hz
  have hn := visibleConnectorGradientOrder_planarGradient hSourceOuter hSourceInner
    hTargetInner hTargetOuter hnS hU hG hKU' hNeg' hTraceOuter' hTraceInner'
      hDisjoint' hci hco
  rw [hInsideInner,← seamComplexCoord.image_closure,hInsideOuter]
  rintro q ⟨z,hz,rfl⟩
  exact mem_image_of_mem _ (hn hz)

end
end TightVer401
