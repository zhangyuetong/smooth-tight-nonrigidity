import TightVer401.VisibleConnectorGradientInverseApplication
import TightVer401.VisibleConnectorCartesianPotentialApplication

/-! Ordinary raw ruling data construct the SAME raw scalar first, then its
actual gradient charts. Reverse gradient Jordan nesting is an ordinary input;
final seam rebasing and the full original Gin open germ remain separate. -/
namespace TightVer401
noncomputable section
open Set Function OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
open scoped Topology ContDiff Matrix
set_option backward.isDefEq.respectTransparency false

/-- No scalar, gradient chart, inverse or degree conclusion is an input.
The raw scalar and all its first jets are retained while constructing the
actual gradient charts from ordinary literal target boundary data. -/
theorem visibleConnectorGradientInverseApplication_raw
    {L : ℝ} (hL : 0 < L) {p gamma w : ℝ → Coord} {g h : ℝ → ℝ}
    (hp : ContDiff ℝ ∞ p) (hgamma : ContDiff ℝ ∞ gamma) (hw : ContDiff ℝ ∞ w)
    (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h)
    (hpL : Periodic p L) (hgammaL : Periodic gamma L) (hwL : Periodic w L)
    (hgL : Periodic g L) (hhL : Periodic h L) (hpos : ∀ s, 0 < h s)
    (hvalue : ∀ s, deriv g s = gamma s ⬝ᵥ deriv p s)
    (hA : ∀ s, 0 < visibleConnectorA p w s) (hB : ∀ s, 0 < visibleConnectorB gamma w s)
    (hDelta : ∀ q : Coord, 0 ≤ q 1 → q 1 ≤ h (q 0) → 0 < visibleConnectorDelta p gamma w q)
    {Ho Hi : ℂ ≃ₜ ℂ}
    (hOuter : PositiveJordanParametrization Ho
      (fun t => seamComplexCoord.symm (p (L*t) + h (L*t) • w (L*t))))
    (hInner : PositiveJordanParametrization Hi (fun t => seamComplexCoord.symm (p (L*t))))
    (hNested : closure (jordanInterior Hi) ⊆ jordanInterior Ho)
    {To Ti : ℂ ≃ₜ ℂ}
    (hGradientIncoming : PositiveJordanParametrization To
      (fun t => seamComplexCoord.symm (gamma (L*t))))
    (hGradientTerminal : PositiveJordanParametrization Ti
      (fun t => seamComplexCoord.symm (visibleConnectorGradient p gamma w ![L*t,h (L*t)])))
    (hGradientNested : closure (jordanInterior Ti) ⊆ jordanInterior To) :
    ∃ (Es : OpenPartialHomeomorph Coord Coord) (G : Coord → ℝ) (U : Set Coord),
      (Es : Coord → Coord) = visibleConnectorCartesianSource L p w h ∧
      ContDiffOn ℝ ∞ Es.symm Es.target ∧
      G = visibleConnectorCartesianPotential L g gamma w h Es ∧
      IsOpen U ∧ annularCoordJordanClosure Ho Hi ⊆ U ∧ U ⊆ Es.target ∧
      ContDiffOn ℝ ∞ G U ∧ (∀ y ∈ U, (planarHessian G y).det < 0) ∧
      (∀ s : ℝ, p s ∈ U ∧ G (p s) = g s ∧ planarGradient G (p s) = gamma s ∧
        p s + h s • w s ∈ U ∧
        G (p s + h s • w s) = g s + h s*(gamma s ⬝ᵥ w s) ∧
        planarGradient G (p s + h s • w s) = visibleConnectorGradient p gamma w ![s,h s]) ∧
    ∃ (P Eg : OpenPartialHomeomorph Coord Coord)
      (HG : ↥(closure (annularCoordJordanInterior Ho Hi)) ≃ₜ
        ↥(closure (annularCoordJordanInterior To Ti))),
      P = visibleConnectorGradientInverseApplication_restricted_chart Eg
        (annularCoordJordanInterior Ho Hi) (annularCoordJordanInterior_isOpen Ho Hi) ∧
      P.source = annularCoordJordanInterior Ho Hi ∧
      P.target = annularCoordJordanInterior To Ti ∧
      (P : Coord → Coord) = planarGradient G ∧
      ContDiffOn ℝ ∞ P (annularCoordJordanInterior Ho Hi) ∧
      ContDiffOn ℝ ∞ P.symm (annularCoordJordanInterior To Ti) ∧
      (∀ z, (HG z : Coord) = planarGradient G z) ∧
      planarGradient G '' closure (annularCoordJordanInterior Ho Hi) =
        closure (annularCoordJordanInterior To Ti) ∧
      closure (annularCoordJordanInterior Ho Hi) ⊆ Eg.source ∧ Eg.source ⊆ U ∧
      ContDiffOn ℝ ∞ G Eg.source ∧
      (∀ z ∈ Eg.source, (planarHessian G z).det < 0) ∧
      (Eg : Coord → Coord) = planarGradient G ∧
      ContDiffOn ℝ ∞ Eg Eg.source ∧ ContDiffOn ℝ ∞ Eg.symm Eg.target ∧
      closure (annularCoordJordanInterior To Ti) ⊆ Eg.target ∧
      EqOn Eg P (annularCoordJordanInterior Ho Hi) ∧
      EqOn Eg.symm P.symm (annularCoordJordanInterior To Ti) ∧
      Eg.target = planarGradient G '' Eg.source := by
  obtain ⟨e0,Es,Hsource,G,U,_he0S,_he0T,_he0F,_hi0,_hH,_hImage,_hKSource,
    _hSourcePositive,_hSourceSmooth,_hJac,hEs,hiEs,_hBandTarget,_hAgree,hGActual,
    hU,hKU,hUT,hGS,hNeg,_hMap,_hHeight,_hGradient,_hAction,_hDet,hBoundary⟩ :=
    visibleConnectorCartesianPotentialApplication_global hL hp hgamma hw hg hh
      hpL hgammaL hwL hgL hhL hpos hvalue hA hB hDelta hOuter hInner hNested
  have hTraceOuter : ∀ t,
      annularComplexConjugate (planarGradient G)
        (seamComplexCoord.symm (p (L*t)+h (L*t) • w (L*t))) =
      seamComplexCoord.symm (visibleConnectorGradient p gamma w ![L*t,h (L*t)]) := by
    intro t
    simp only [annularComplexConjugate,Function.comp_apply,seamComplexCoord.apply_symm_apply]
    rw [(hBoundary (L*t)).2.2.2.2.2]
  have hTraceInner : ∀ t,
      annularComplexConjugate (planarGradient G) (seamComplexCoord.symm (p (L*t))) =
      seamComplexCoord.symm (gamma (L*t)) := by
    intro t
    simp only [annularComplexConjugate,Function.comp_apply,seamComplexCoord.apply_symm_apply]
    rw [(hBoundary (L*t)).2.2.1]
  refine ⟨Es,G,U,hEs,hiEs,hGActual,hU,hKU,hUT,hGS,hNeg,hBoundary,?_⟩
  exact visibleConnectorGradientInverseApplication_charts hOuter hInner hGradientTerminal
    hGradientIncoming hNested hGradientNested hU hGS hKU (fun y hy => hNeg y (hKU hy))
    hTraceOuter hTraceInner

end
end TightVer401
