import TightVer401.VisibleConnectorWitnessAssemblyTopology
import TightVer401.VisibleConnectorOrdinaryFamilyRebasedRawPotential
import TightVer401.VisibleConnectorOrdinaryFamilyRebasedTopology

/-! Actual source geometry assembles the SAME raw inverse/potential. The
incoming filling constructs its own norm bound; the actual terminal det/turn,
frontier and origin facts yield the positive rebased boundary. Source
separation follows from the norm margin, upstream of final smoothing. -/
namespace TightVer401
noncomputable section
open Set Function Filter OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
open scoped Topology ContDiff Matrix
set_option backward.isDefEq.respectTransparency false

/-- A norm bound chosen from compactness of the actual SAME incoming filling.
Choose eta with this M before constructing its displaced family. -/
def visibleConnectorOrdinaryFamilyGeometricRawBound (Hi : ℂ ≃ₜ ℂ) : ℝ :=
  Classical.choose (visibleConnectorOrdinaryFamily_jordan_closure_norm_bound Hi)

/-- The bound is constructed, including every physical incoming phase. -/
theorem visibleConnectorOrdinaryFamilyGeometricRaw_bound
    {L : ℝ} (hL : 0 < L) {incoming : ℝ → Coord} (Hi : ℂ ≃ₜ ℂ)
    (hInner : PositiveJordanParametrization Hi
      (fun t => seamComplexCoord.symm (incoming (L * t)))) :
    0 ≤ visibleConnectorOrdinaryFamilyGeometricRawBound Hi ∧
    ∀ s, ‖positiveExitComplexTrace incoming s‖ ≤
      visibleConnectorOrdinaryFamilyGeometricRawBound Hi := by
  have hB := Classical.choose_spec (visibleConnectorOrdinaryFamily_jordan_closure_norm_bound Hi)
  refine ⟨hB.1, ?_⟩
  intro s
  have hclock : L * (s / L) = s := by field_simp [hL.ne']
  have hs := hInner.toRegular.mem_frontier (s / L)
  rw [hclock] at hs
  have he := hB.2 _ (frontier_subset_closure hs)
  simpa only [positiveExitComplexTrace, Function.comp_apply, visibleConnectorOrdinaryFamilyGeometricRawBound,
    visibleConnectorWitnessAssemblyTopology_complex_point] using he

/-- Assemble the raw E/U/B from actual terminal geometry. The supplied
incoming filling and its origin are previously constructed ordinary incoming
facts. No terminal positive-Jordan, disjointness or nesting input remains. -/
theorem visibleConnectorOrdinaryFamilyGeometricRaw_actual
    {L : ℝ} (hL : 0 < L) {p gamma w incoming : ℝ → Coord} {g a b : ℝ → ℝ}
    (hp : ContDiff ℝ ∞ p) (hgamma : ContDiff ℝ ∞ gamma) (hw : ContDiff ℝ ∞ w)
    (hg : ContDiff ℝ ∞ g) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpL : Periodic p L) (hgammaL : Periodic gamma L) (hwL : Periodic w L)
    (hgL : Periodic g L) (hshift : ∀ s, a (s + L) = a s + L) (hbL : Periodic b L)
    (hap : ∀ s, 0 < deriv a s) (hbneg : ∀ s, b s < 0)
    (hA : ∀ s, 0 < visibleConnectorA p w s)
    (hB : ∀ s, 0 < visibleConnectorB gamma w s)
    (hC : ∀ s, 0 < visibleConnectorC gamma w s)
    (hLower : ∀ s, 0 < visibleConnectorDelta p gamma w ![a s, b s])
    (hvalue : ∀ s, deriv g s = gamma s ⬝ᵥ deriv p s)
    (hIncoming : ∀ s, visibleConnectorRebasedSource p w a b s = incoming s)
    {Ho Hi : ℂ ≃ₜ ℂ}
    (hInner : PositiveJordanParametrization Hi
      (fun t => seamComplexCoord.symm (incoming (L * t))))
    (hcInner : (0 : ℂ) ∈ jordanInterior Hi)
    (hTerminalInj : InjOn (visibleConnectorActualTerminalSource p gamma w) (Ico (0 : ℝ) L))
    (hTerminalNonzero : ∀ s, positiveExitComplexTrace
      (visibleConnectorActualTerminalSource p gamma w) s ≠ 0)
    (hTerminalDet : ∀ s, 0 < visibleConnectorDet
      (visibleConnectorActualTerminalSource p gamma w s)
      (deriv (visibleConnectorActualTerminalSource p gamma w) s))
    (hTerminalTurn : HasPositiveArgumentTurn
      (positiveExitComplexTrace (visibleConnectorActualTerminalSource p gamma w)) L)
    (hTerminalFrontier : range (positiveExitComplexTrace
      (visibleConnectorActualTerminalSource p gamma w)) = frontier (jordanInterior Ho))
    (hcOuter : (0 : ℂ) ∈ jordanInterior Ho)
    (hTerminalNorm : ∀ s, visibleConnectorOrdinaryFamilyGeometricRawBound Hi <
      ‖positiveExitComplexTrace (visibleConnectorActualTerminalSource p gamma w) s‖) :
    let tc := visibleConnectorActualTerminalHeight p gamma w
    let d := fun s => tc (a s) - b s
    let P := visibleConnectorRebasedSource p w a b
    let f := visibleConnectorRebasedHeight g gamma w a b
    let W := visibleConnectorRebasedRuling w a d
    let Gamma := visibleConnectorRebasedGradient p gamma w a b
    let h := fun _ : ℝ => (1 : ℝ)
    ∃ (e0 E : OpenPartialHomeomorph Coord Coord)
      (H : ↥{z : Coord | 1 ≤ planarRadius z ∧ planarRadius z ≤ 2} ≃ₜ
        annularCoordJordanClosure Ho Hi) (B : Coord → ℝ) (U : Set Coord),
      e0.source = {z : Coord | 1 < planarRadius z ∧ planarRadius z < 2} ∧
      e0.target = annularCoordJordanInterior Ho Hi ∧
      (e0 : Coord → Coord) = visibleConnectorCartesianSource L P W h ∧
      ContDiffOn ℝ ∞ e0.symm e0.target ∧
      (∀ z, (H z : Coord) = visibleConnectorCartesianSource L P W h z) ∧
      visibleConnectorCartesianSource L P W h ''
        {z : Coord | 1 ≤ planarRadius z ∧ planarRadius z ≤ 2} = annularCoordJordanClosure Ho Hi ∧
      {z : Coord | 1 ≤ planarRadius z ∧ planarRadius z ≤ 2} ⊆ E.source ∧
      E.source ⊆ {z : Coord | 0 < planarRadius z} ∧
      ContDiffOn ℝ ∞ (visibleConnectorCartesianSource L P W h) E.source ∧
      (∀ z ∈ E.source, 0 < annularJacobian (visibleConnectorCartesianSource L P W h) z) ∧
      (E : Coord → Coord) = visibleConnectorCartesianSource L P W h ∧
      ContDiffOn ℝ ∞ E.symm E.target ∧
      annularCoordJordanClosure Ho Hi ⊆ E.target ∧
      EqOn E.symm e0.symm (annularCoordJordanInterior Ho Hi) ∧
      B = visibleConnectorCartesianPotential L f Gamma W h E ∧
      IsOpen U ∧ annularCoordJordanClosure Ho Hi ⊆ U ∧ U ⊆ E.target ∧
      ContDiffOn ℝ ∞ B U ∧ (∀ y ∈ U, (planarHessian B y).det < 0) ∧
      MapsTo (visibleConnectorSource P W) (visibleConnectorCartesianPotentialRuledDomain L P Gamma W h E) U ∧
      EqOn (B ∘ visibleConnectorSource P W) (visibleConnectorHeight f Gamma W)
        (visibleConnectorCartesianPotentialRuledDomain L P Gamma W h E) ∧
      EqOn (planarGradient B ∘ visibleConnectorSource P W) (visibleConnectorGradient P Gamma W)
        (visibleConnectorCartesianPotentialRuledDomain L P Gamma W h E) ∧
      (∀ q ∈ visibleConnectorCartesianPotentialRuledDomain L P Gamma W h E,
        planarHessian B (visibleConnectorSource P W q) *ᵥ W (q 0) =
          (visibleConnectorA P W (q 0)*visibleConnectorB Gamma W (q 0) /
            (visibleConnectorDelta P Gamma W q)^2) • visibleConnectorJ (W (q 0))) ∧
      (∀ q ∈ visibleConnectorCartesianPotentialRuledDomain L P Gamma W h E,
        (planarHessian B (visibleConnectorSource P W q)).det =
          -(visibleConnectorA P W (q 0))^2*(visibleConnectorB Gamma W (q 0))^2 /
            (visibleConnectorDelta P Gamma W q)^4) ∧
      (∀ s : ℝ, P s ∈ U ∧ B (P s) = f s ∧ planarGradient B (P s) = Gamma s ∧
        P s + h s • W s ∈ U ∧
        B (P s + h s • W s) = f s + h s*(Gamma s ⬝ᵥ W s) ∧
        planarGradient B (P s + h s • W s) = visibleConnectorGradient P Gamma W ![s,h s]) := by
  let tc := visibleConnectorActualTerminalHeight p gamma w
  let T := visibleConnectorActualTerminalSource p gamma w
  have htc : ContDiff ℝ ∞ tc :=
    visibleConnectorActualTerminalHeight_contDiff hp hgamma hw (fun s => (hC s).ne')
  obtain ⟨_htc, htcL, _htcpos, _hd, _hdL, _hdpos, _hUpper,
    _hP, _hf, _hW, _hGamma, _hPL, _hfL, _hWL, _hGammaL, _hval, _hANew, _hBNew,
    _hClosed, _hOut⟩ :=
    visibleConnectorOrdinaryFamilyRebasedCoefficients_actual hp hgamma hw hg ha hb
      hpL hgammaL hwL hgL hshift hbL hap hbneg hA hB hC hLower hvalue
  change Periodic tc L at htcL
  have hT : ContDiff ℝ ∞ T := hp.add (htc.smul hw)
  have hTL : Periodic T L := by
    intro s
    change p (s + L) + tc (s + L) • w (s + L) = p s + tc s • w s
    rw [hpL s, htcL s, hwL s]
  obtain ⟨hPositive, _hRange, _hFrontier⟩ :=
    visibleConnectorOrdinaryFamily_rebased_same_positive_jordan hL Ho hT ha hTL
      hTerminalInj hTerminalNonzero hTerminalDet hTerminalTurn hap hshift
      hTerminalFrontier hcOuter
  have hOuter : PositiveJordanParametrization Ho (fun t => seamComplexCoord.symm
      (p (a (L * t)) + visibleConnectorActualTerminalHeight p gamma w (a (L * t)) •
        w (a (L * t)))) := by
    have heTrace : visibleConnectorTerminalNormalizedTrace L (fun s => T (a s)) =
        (fun t => seamComplexCoord.symm
          (p (a (L * t)) + tc (a (L * t)) • w (a (L * t)))) := by
      funext t
      exact visibleConnectorWitnessAssemblyTopology_complex_point (T (a (L * t)))
    rw [heTrace] at hPositive
    exact hPositive
  have hNorm := (visibleConnectorOrdinaryFamilyGeometricRaw_bound hL Hi hInner).2
  have hDisjoint : Disjoint (range incoming)
      (range (fun s => p (a s) + tc (a s) • w (a s))) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨s, rfl⟩ ⟨t, ht⟩
    change p (a t) + tc (a t) • w (a t) = incoming s at ht
    have hn := hTerminalNorm (a t)
    change visibleConnectorOrdinaryFamilyGeometricRawBound Hi <
      ‖positiveExitComplexPoint (p (a t) + tc (a t) • w (a t))‖ at hn
    rw [ht] at hn
    exact (not_lt_of_ge (hNorm s)) hn
  exact visibleConnectorOrdinaryFamilyRebasedRawPotential_actual hL
    hp hgamma hw hg ha hb hpL hgammaL hwL hgL hshift hbL hap hbneg
    hA hB hC hLower hvalue hIncoming hOuter hInner hDisjoint hcOuter hcInner

end
end TightVer401
