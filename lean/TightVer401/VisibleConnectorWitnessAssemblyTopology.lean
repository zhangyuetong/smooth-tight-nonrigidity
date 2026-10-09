import TightVer401.DualRadialCompletionExitApplicationGeometry
import TightVer401.AnnularDegreeBoundaryHomeomorphs

/-! Ordinary physical trace topology for the canonical connector witness.
The same supplied Jordan fillings are retained through the positive period
clock. Nesting remains an ordinary geometric input; no connector, inverse,
or potential construction is assumed or produced here. -/
namespace TightVer401
noncomputable section
open Set Function Metric OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
open scoped ContDiff Topology

/-- The physical complex trace uses exactly the existing seam coordinates. -/
theorem visibleConnectorWitnessAssemblyTopology_complex_point (q : Coord) :
    positiveExitComplexPoint q = seamComplexCoord.symm q := by
  apply seamComplexCoord.injective
  rw [dualRadialCompletionExitApplication_coord_complex,
    seamComplexCoord.apply_symm_apply]

/-- The completion trace has the six fields of the pinned positive Jordan
interface, with the same filling and the same parametrized curve. -/
theorem visibleConnectorWitnessAssemblyTopology_positiveJordan
    {H : ℂ ≃ₜ ℂ} {f : ℝ → ℂ} (h : DualRadialCompletionPositiveTrace H f) :
    PositiveJordanParametrization H f :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- Normalize an ordinary physical exit trace by its actual positive period.
The already proved winding producer chooses its fillings once; all subsequent
inside and boundary identities refer to those same fillings. -/
theorem visibleConnectorWitnessAssemblyTopology_positive_traces
    {G : Coord → ℝ} {U : Set Coord} {L : ℝ} (X : PositiveExitTrace G U L) :
    ∃ Hp Hg : ℂ ≃ₜ ℂ,
      PositiveJordanParametrization Hp (fun t => seamComplexCoord.symm (X.p (L*t))) ∧
      PositiveJordanParametrization Hg (fun t => seamComplexCoord.symm (X.gamma (L*t))) ∧
      (0 : ℂ) ∈ jordanInterior Hp ∧ (0 : ℂ) ∈ jordanInterior Hg ∧
      positiveExitInside X.p = seamComplexCoord '' jordanInterior Hp ∧
      positiveExitInside X.gamma = seamComplexCoord '' jordanInterior Hg := by
  obtain ⟨Hp,Hg,hp,hg,hp0,hg0,hpInside,hgInside⟩ :=
    dualRadialCompletionExitApplicationPeriod_positive_traces X
  have hp' := visibleConnectorWitnessAssemblyTopology_positiveJordan hp
  have hg' := visibleConnectorWitnessAssemblyTopology_positiveJordan hg
  have hpc : (fun t => positiveExitComplexTrace X.p (L*t)) =
      (fun t => seamComplexCoord.symm (X.p (L*t))) := by
    funext t
    exact visibleConnectorWitnessAssemblyTopology_complex_point (X.p (L*t))
  have hgc : (fun t => positiveExitComplexTrace X.gamma (L*t)) =
      (fun t => seamComplexCoord.symm (X.gamma (L*t))) := by
    funext t
    exact visibleConnectorWitnessAssemblyTopology_complex_point (X.gamma (L*t))
  rw [hpc] at hp'
  rw [hgc] at hg'
  exact ⟨Hp,Hg,hp',hg',hp0,hg0,hpInside,hgInside⟩

/-- A normalized positive boundary describes the full physical boundary,
including every phase of the original period. The inside belongs to the same
supplied filling, using the ordinary native Jordan evidence for the curve. -/
theorem visibleConnectorWitnessAssemblyTopology_physical_geometry
    {L : ℝ} (hL : 0 < L) {p : ℝ → Coord} {H : ℂ ≃ₜ ℂ}
    (hPositive : PositiveJordanParametrization H
      (fun t => seamComplexCoord.symm (p (L*t))))
    (hJordan : Schoenflies.IsJordanCurve (positiveExitJordanRange p)) :
    range p = seamComplexCoord '' frontier (jordanInterior H) ∧
      positiveExitInside p = seamComplexCoord '' jordanInterior H := by
  have hNormalized : DualRadialCompletionPositiveTrace H
      (fun t => positiveExitComplexTrace p (L*t)) := by
    have h : DualRadialCompletionPositiveTrace H
        (fun t => seamComplexCoord.symm (p (L*t))) :=
      ⟨hPositive.smooth,hPositive.periodic,hPositive.injective,hPositive.regular,
        hPositive.boundary,hPositive.positive⟩
    have he : (fun t => positiveExitComplexTrace p (L*t)) =
        (fun t => seamComplexCoord.symm (p (L*t))) := by
      funext t
      exact visibleConnectorWitnessAssemblyTopology_complex_point (p (L*t))
    rw [he]
    exact h
  have hRange : range (positiveExitComplexTrace p) = H '' sphere (0 : ℂ) 1 := by
    rw [← dualRadialCompletionExitApplicationPeriod_range hL (positiveExitComplexTrace p)]
    exact dualRadialCompletion_positiveTrace_range hNormalized
  have hFrontRange : range (positiveExitComplexTrace p) = frontier (jordanInterior H) := by
    change range (positiveExitComplexTrace p) = frontier (H '' ball (0 : ℂ) 1)
    rw [← H.image_frontier,frontier_ball _ one_ne_zero]
    exact hRange
  have hPhysical : range p = seamComplexCoord '' range (positiveExitComplexTrace p) := by
    rw [← range_comp]
    congr 1
    funext s
    exact (dualRadialCompletionExitApplication_coord_complex (p s)).symm
  exact ⟨hPhysical.trans (congrArg (fun S => seamComplexCoord '' S) hFrontRange),
    dualRadialCompletionTraceInside_eq_of_range hRange hJordan⟩

/-- Strict physical nesting transports all annulus topology to the same
ordinary normalized Jordan boundaries. The frontier order matches the
canonical connector contract: inner physical curve followed by outer. -/
theorem visibleConnectorWitnessAssemblyTopology_annulus_geometry
    {L : ℝ} (hL : 0 < L) {outer inner : ℝ → Coord} {Ho Hi : ℂ ≃ₜ ℂ}
    (hOuter : PositiveJordanParametrization Ho
      (fun t => seamComplexCoord.symm (outer (L*t))))
    (hInner : PositiveJordanParametrization Hi
      (fun t => seamComplexCoord.symm (inner (L*t))))
    (hOuterJordan : Schoenflies.IsJordanCurve (positiveExitJordanRange outer))
    (hInnerJordan : Schoenflies.IsJordanCurve (positiveExitJordanRange inner))
    (hNested : closure (positiveExitInside inner) ⊆ positiveExitInside outer) :
    closure (jordanInterior Hi) ⊆ jordanInterior Ho ∧
      positiveExitInside outer \ closure (positiveExitInside inner) =
        annularCoordJordanInterior Ho Hi ∧
      IsOpen (positiveExitInside outer \ closure (positiveExitInside inner)) ∧
      IsCompact (closure (positiveExitInside outer \ closure (positiveExitInside inner))) ∧
      closure (positiveExitInside outer \ closure (positiveExitInside inner)) =
        annularCoordJordanClosure Ho Hi ∧
      frontier (positiveExitInside outer \ closure (positiveExitInside inner)) =
        range inner ∪ range outer ∧
      Disjoint (range inner) (range outer) := by
  obtain ⟨hOuterRange,hOuterInside⟩ :=
    visibleConnectorWitnessAssemblyTopology_physical_geometry hL hOuter hOuterJordan
  obtain ⟨hInnerRange,hInnerInside⟩ :=
    visibleConnectorWitnessAssemblyTopology_physical_geometry hL hInner hInnerJordan
  have hn : closure (jordanInterior Hi) ⊆ jordanInterior Ho :=
    dualRadialCompletionExitApplication_nested hOuterInside hInnerInside hNested
  have hAnn : positiveExitInside outer \ closure (positiveExitInside inner) =
      annularCoordJordanInterior Ho Hi :=
    dualRadialCompletionExitApplication_annulus hOuterInside hInnerInside
  have hClosed : closure (positiveExitInside outer \ closure (positiveExitInside inner)) =
      annularCoordJordanClosure Ho Hi := by
    rw [hAnn,closure_annularCoordJordanInterior Ho Hi hn]
  have hFront : frontier (positiveExitInside outer \ closure (positiveExitInside inner)) =
      range inner ∪ range outer := by
    rw [hAnn,frontier_annularCoordJordanInterior Ho Hi hn]
    change seamComplexCoord '' (frontier (jordanInterior Ho) ∪
      frontier (jordanInterior Hi)) = range inner ∪ range outer
    rw [image_union,← hOuterRange,← hInnerRange,union_comm]
  have hDisjoint : Disjoint (range inner) (range outer) := by
    rw [hInnerRange,hOuterRange]
    apply Set.disjoint_left.mpr
    intro q hqi hqo
    obtain ⟨zi,hzi,hiz⟩ := hqi
    obtain ⟨zo,hzo,hoz⟩ := hqo
    have he : zi = zo := seamComplexCoord.injective (hiz.trans hoz.symm)
    exact (Set.disjoint_left.mp (annular_nested_jordan_frontiers_disjoint hn))
      hzo (he ▸ hzi)
  refine ⟨hn,hAnn,?_,?_,hClosed,hFront,hDisjoint⟩
  · rw [hAnn]
    exact annularCoordJordanInterior_isOpen Ho Hi
  · rw [hClosed]
    exact annularCoordJordanClosure_isCompact Ho Hi

end
end TightVer401
