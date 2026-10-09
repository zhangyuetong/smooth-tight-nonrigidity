import TightVer401.PositiveExitConstructionSelectedSourceGeometryRawBoundary
import TightVer401.PositiveExitConstructionSelectedSourceGeometryRawAnnulus

/-! Actual raw selected source construction. Both positive Jordan fillings,
separation and common origin enclosures are produced from the original raw
leaves and retained source margins. Signed order then produces strict nesting,
the exact full flow-core annulus and its actual Cartesian inverse. No desired
raw geometry or independent source-map package is assumed. -/
namespace TightVer401
noncomputable section
open Set Function MeasureTheory OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- Construct all ordinary raw source geometry from the SAME original seed,
complete flow, selected initial values, source margin and original chart. -/
theorem positiveExitSelected_exists_raw_source_construction
    {T δ w : ℝ} [Fact (0 < T)] (d : PeriodicRuledFrame T)
    (hb : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0)
    (hinside : ∀ u ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 u t ∈ Ioo 0 w)
    (vin vout : Ioo (0 : ℝ) δ) (horder : (vin : ℝ) < (vout : ℝ))
    (hNi : Injective (d.bandGaussMap (b := w)))
    (hnorth : ∀ p : AddCircle T × Ioo (0 : ℝ) w, 0 < d.bandGaussMap p 2)
    (horient : ∀ s, ambientCross (d.T s) (d.E s) = d.n s)
    (hmargin : ∀ v : Ioo (0 : ℝ) δ,
      (∀ s, angularDescentComplex (gnomonicInverse (positiveExitRawLeaf d hb hinside v s)) ≠ 0) ∧
      HasPositiveArgumentTurn
        (angularDescentComplex ∘ gnomonicInverse ∘ positiveExitRawLeaf d hb hinside v) T)
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) Coord)
    (heF : ∀ p, e p = gnomonicInverse (d.bandGaussMap p)) :
    ∃ Ho Hi : ℂ ≃ₜ ℂ,
      PositiveJordanParametrization Ho (positiveExitSelected_rawBoundary d hb hinside vout) ∧
      PositiveJordanParametrization Hi (positiveExitSelected_rawBoundary d hb hinside vin) ∧
      DualRadialCompletionPositiveTrace Ho (positiveExitSelected_rawBoundary d hb hinside vout) ∧
      DualRadialCompletionPositiveTrace Hi (positiveExitSelected_rawBoundary d hb hinside vin) ∧
      (0 : ℂ) ∈ jordanInterior Ho ∧ (0 : ℂ) ∈ jordanInterior Hi ∧
      closure (jordanInterior Hi) ⊆ jordanInterior Ho ∧
      positiveExit_selectedSourceGeometry_flowCore d hb hinside e vin vout =
        annularCoordJordanInterior Ho Hi ∧
      ∃ e0 : OpenPartialHomeomorph Coord Coord,
        e0.source = {p : Coord | 1 < planarRadius p ∧ planarRadius p < 2} ∧
        e0.target = positiveExit_selectedSourceGeometry_flowCore d hb hinside e vin vout ∧
        (e0 : Coord → Coord) = positiveExitSelected_roundCartesianSource d vin vout ∧
        ContDiffOn ℝ ∞ e0.symm e0.target := by
  obtain ⟨Ho, hOuter, hOuterTrace, hOuter0⟩ :=
    positiveExitSelected_rawBoundary_exists_positive_jordan d hb hinside vout hNi hnorth
      (hmargin vout).1 (hmargin vout).2
  obtain ⟨Hi, hInner, hInnerTrace, hInner0⟩ :=
    positiveExitSelected_rawBoundary_exists_positive_jordan d hb hinside vin hNi hnorth
      (hmargin vin).1 (hmargin vin).2
  have hRanges := positiveExitSelected_rawBoundary_ranges_disjoint d hb hinside vin vout horder hNi hnorth
  have hDisjoint : Disjoint (frontier (jordanInterior Ho)) (frontier (jordanInterior Hi)) := by
    apply Set.disjoint_left.mpr
    intro z hzo hzi
    have hzoR : z ∈ range (positiveExitSelected_rawBoundary d hb hinside vout) := by
      rw [← hOuter.boundary] at hzo
      exact image_subset_range _ _ hzo
    have hziR : z ∈ range (positiveExitSelected_rawBoundary d hb hinside vin) := by
      rw [← hInner.boundary] at hzi
      exact image_subset_range _ _ hzi
    exact Set.disjoint_left.mp hRanges hziR hzoR
  have hActual := positiveExitSelected_rawAnnulus_order_and_image d hb hinside vin vout horder
    hnorth horient e heF hOuter hInner hDisjoint hOuter0 hInner0
  exact ⟨Ho, Hi, hOuter, hInner, hOuterTrace, hInnerTrace, hOuter0, hInner0,
    hActual.1, hActual.2.1, hActual.2.2⟩

end
end TightVer401
