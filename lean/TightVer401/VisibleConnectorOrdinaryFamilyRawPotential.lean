import TightVer401.VisibleConnectorOrdinaryFamilySourceChart
import TightVer401.VisibleConnectorSourceOrderRound
import TightVer401.VisibleConnectorCartesianPotentialApplication

/-! Actual raw E/U/B assembly from endpoint geometry. Source nesting is
proved by signed order of the literal Cartesian ruling. One raw scalar B is
constructed on an open carrier covering the full closed target band, contained
in the SAME E.target. This is upstream of final smoothing; neither a final-H
inverse nor an incoming scalar germ is substituted for raw construction. -/
namespace TightVer401
noncomputable section
open Set Function Filter OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
open scoped Topology ContDiff Matrix
set_option backward.isDefEq.respectTransparency false

private theorem rawPotential_range_boundary {H : ℂ ≃ₜ ℂ} {eta : ℝ → ℂ}
    (h : PositiveJordanParametrization H eta) :
    range eta = frontier (jordanInterior H) := by
  apply Subset.antisymm
  · rintro z ⟨t, rfl⟩
    exact h.toRegular.mem_frontier t
  · intro z hz
    rw [← h.boundary] at hz
    exact image_subset_range _ _ hz

/-- Construct ONE actual raw source inverse and saddle carrier/scalar from
smooth periodic ruling data, actual endpoint determinant signs, disjoint
physical boundaries and common-origin enclosure. No source nesting or
Cartesian Jacobian sign is assumed. All literal closed-band and first-jet
outputs of the raw-potential producer are retained. -/
theorem visibleConnectorOrdinaryFamilyRawPotential_global
    {L : ℝ} (hL : 0 < L) {p gamma w : ℝ → Coord} {g h : ℝ → ℝ}
    (hp : ContDiff ℝ ∞ p) (hgamma : ContDiff ℝ ∞ gamma) (hw : ContDiff ℝ ∞ w)
    (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h)
    (hpL : Periodic p L) (hgammaL : Periodic gamma L) (hwL : Periodic w L)
    (hgL : Periodic g L) (hhL : Periodic h L) (hpos : ∀ s, 0 < h s)
    (hvalue : ∀ s, deriv g s = gamma s ⬝ᵥ deriv p s)
    (hLower : ∀ s, visibleConnectorDet (deriv p s) (w s) < 0)
    (hUpper : ∀ s, visibleConnectorDet (deriv p s + h s • deriv w s) (w s) < 0)
    (hB : ∀ s, 0 < visibleConnectorB gamma w s)
    {Ho Hi : ℂ ≃ₜ ℂ}
    (hOuter : PositiveJordanParametrization Ho
      (fun t => seamComplexCoord.symm (p (L*t) + h (L*t) • w (L*t))))
    (hInner : PositiveJordanParametrization Hi (fun t => seamComplexCoord.symm (p (L*t))))
    (hDisjoint : Disjoint (range p) (range (fun s => p s + h s • w s)))
    (hcOuter : (0 : ℂ) ∈ jordanInterior Ho) (hcInner : (0 : ℂ) ∈ jordanInterior Hi) :
    ∃ (e0 E : OpenPartialHomeomorph Coord Coord)
      (H : ↥{z : Coord | 1 ≤ planarRadius z ∧ planarRadius z ≤ 2} ≃ₜ
        annularCoordJordanClosure Ho Hi) (B : Coord → ℝ) (U : Set Coord),
      e0.source = {z : Coord | 1 < planarRadius z ∧ planarRadius z < 2} ∧
      e0.target = annularCoordJordanInterior Ho Hi ∧
      (e0 : Coord → Coord) = visibleConnectorCartesianSource L p w h ∧
      ContDiffOn ℝ ∞ e0.symm e0.target ∧
      (∀ z, (H z : Coord) = visibleConnectorCartesianSource L p w h z) ∧
      visibleConnectorCartesianSource L p w h ''
        {z : Coord | 1 ≤ planarRadius z ∧ planarRadius z ≤ 2} = annularCoordJordanClosure Ho Hi ∧
      {z : Coord | 1 ≤ planarRadius z ∧ planarRadius z ≤ 2} ⊆ E.source ∧
      E.source ⊆ {z : Coord | 0 < planarRadius z} ∧
      ContDiffOn ℝ ∞ (visibleConnectorCartesianSource L p w h) E.source ∧
      (∀ z ∈ E.source, 0 < annularJacobian (visibleConnectorCartesianSource L p w h) z) ∧
      (E : Coord → Coord) = visibleConnectorCartesianSource L p w h ∧
      ContDiffOn ℝ ∞ E.symm E.target ∧
      annularCoordJordanClosure Ho Hi ⊆ E.target ∧
      EqOn E.symm e0.symm (annularCoordJordanInterior Ho Hi) ∧
      B = visibleConnectorCartesianPotential L g gamma w h E ∧
      IsOpen U ∧ annularCoordJordanClosure Ho Hi ⊆ U ∧ U ⊆ E.target ∧
      ContDiffOn ℝ ∞ B U ∧ (∀ y ∈ U, (planarHessian B y).det < 0) ∧
      MapsTo (visibleConnectorSource p w) (visibleConnectorCartesianPotentialRuledDomain L p gamma w h E) U ∧
      EqOn (B ∘ visibleConnectorSource p w) (visibleConnectorHeight g gamma w)
        (visibleConnectorCartesianPotentialRuledDomain L p gamma w h E) ∧
      EqOn (planarGradient B ∘ visibleConnectorSource p w) (visibleConnectorGradient p gamma w)
        (visibleConnectorCartesianPotentialRuledDomain L p gamma w h E) ∧
      (∀ q ∈ visibleConnectorCartesianPotentialRuledDomain L p gamma w h E,
        planarHessian B (visibleConnectorSource p w q) *ᵥ w (q 0) =
          (visibleConnectorA p w (q 0)*visibleConnectorB gamma w (q 0) /
            (visibleConnectorDelta p gamma w q)^2) • visibleConnectorJ (w (q 0))) ∧
      (∀ q ∈ visibleConnectorCartesianPotentialRuledDomain L p gamma w h E,
        (planarHessian B (visibleConnectorSource p w q)).det =
          -(visibleConnectorA p w (q 0))^2*(visibleConnectorB gamma w (q 0))^2 /
            (visibleConnectorDelta p gamma w q)^4) ∧
      (∀ s : ℝ, p s ∈ U ∧ B (p s) = g s ∧ planarGradient B (p s) = gamma s ∧
        p s + h s • w s ∈ U ∧
        B (p s + h s • w s) = g s + h s*(gamma s ⬝ᵥ w s) ∧
        planarGradient B (p s + h s • w s) = visibleConnectorGradient p gamma w ![s,h s]) := by
  let F := visibleConnectorCartesianSource L p w h
  let O : Set Coord := {q | 0 < planarRadius q}
  obtain ⟨hO, hF, hKO, hJ, _hIncoming, _hTerminal⟩ :=
    visibleConnectorOrdinaryFamilySourceChart_fields hL hp hw hh hpL hwL hhL
      hpos hLower hUpper
  have hBoundaryDisjoint : Disjoint (frontier (jordanInterior Ho))
      (frontier (jordanInterior Hi)) := by
    apply Set.disjoint_left.mpr
    intro z hzo hzi
    rw [← rawPotential_range_boundary hOuter] at hzo
    rw [← rawPotential_range_boundary hInner] at hzi
    obtain ⟨t, ht⟩ := hzo
    obtain ⟨u, hu⟩ := hzi
    have hout : seamComplexCoord z ∈ range (fun s => p s + h s • w s) := by
      refine ⟨L * t, ?_⟩
      rw [← ht]
      exact (seamComplexCoord.apply_symm_apply _).symm
    have hin : seamComplexCoord z ∈ range p := by
      refine ⟨L * u, ?_⟩
      rw [← hu]
      exact (seamComplexCoord.apply_symm_apply _).symm
    exact Set.disjoint_left.mp hDisjoint hin hout
  have hNested : closure (jordanInterior Hi) ⊆ jordanInterior Ho :=
    visibleConnectorSourceOrder_round hO hF hKO hJ hOuter hInner
      (visibleConnectorSourceInverseApplication_outer hpL hwL hhL)
      (visibleConnectorSourceInverseApplication_inner hpL hwL hhL)
      hBoundaryDisjoint hcOuter hcInner
  have hA : ∀ s, 0 < visibleConnectorA p w s := by
    intro s
    exact neg_pos.mpr (hLower s)
  have hDelta : ∀ q : Coord, 0 ≤ q 1 → q 1 ≤ h (q 0) →
      0 < visibleConnectorDelta p gamma w q :=
    fun q hu huh => visibleConnectorOrdinaryFamilySourceChart_delta_closed
      hLower hUpper q hu huh
  exact visibleConnectorCartesianPotentialApplication_global hL hp hgamma hw hg hh
    hpL hgammaL hwL hgL hhL hpos hvalue hA hB hDelta hOuter hInner hNested

end
end TightVer401
