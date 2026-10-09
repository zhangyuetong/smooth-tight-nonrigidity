import TightVer401.VisibleConnectorOrdinaryFamilyRebasedCoefficients
import TightVer401.VisibleConnectorOrdinaryFamilyRawPotential

/-! ONE actual raw inverse/carrier/scalar for the SAME rebased ruling. The
terminal height and remaining length are literal definitions. Analytic rebase
facts and both determinant signs are produced from original coefficients.
The incoming identity and disjoint/enclosing positive boundary geometry
remain explicit until the frozen incoming worker supplies them. -/
namespace TightVer401
noncomputable section
open Set Function Filter OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
open scoped Topology ContDiff Matrix
set_option backward.isDefEq.respectTransparency false

/-- Actual raw E/U/B with the original incoming boundary and the literal old
terminal composed with SAME a. Every raw-potential output is retained. -/
theorem visibleConnectorOrdinaryFamilyRebasedRawPotential_actual
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
    (hOuter : PositiveJordanParametrization Ho (fun t => seamComplexCoord.symm
      (p (a (L * t)) + visibleConnectorActualTerminalHeight p gamma w (a (L * t)) •
        w (a (L * t)))))
    (hInner : PositiveJordanParametrization Hi
      (fun t => seamComplexCoord.symm (incoming (L * t))))
    (hDisjoint : Disjoint (range incoming)
      (range (fun s => p (a s) + visibleConnectorActualTerminalHeight p gamma w (a s) • w (a s))))
    (hcOuter : (0 : ℂ) ∈ jordanInterior Ho) (hcInner : (0 : ℂ) ∈ jordanInterior Hi) :
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
  dsimp only
  let tc := visibleConnectorActualTerminalHeight p gamma w
  let d := fun s => tc (a s) - b s
  let P := visibleConnectorRebasedSource p w a b
  let f := visibleConnectorRebasedHeight g gamma w a b
  let W := visibleConnectorRebasedRuling w a d
  let Gamma := visibleConnectorRebasedGradient p gamma w a b
  let h := fun _ : ℝ => (1 : ℝ)
  obtain ⟨_htc, _htcL, _htcpos, _hd, _hdL, _hdpos, _hUpper,
    hP, hf, hW, hGamma, hPL, hfL, hWL, hGammaL, hval, hANew, hBNew, hClosed, hOut⟩ :=
    visibleConnectorOrdinaryFamilyRebasedCoefficients_actual hp hgamma hw hg ha hb
      hpL hgammaL hwL hgL hshift hbL hap hbneg hA hB hC hLower hvalue
  have hIn : P = incoming := funext hIncoming
  have hOutFn : (fun s => P s + h s • W s) =
      (fun s => p (a s) + tc (a s) • w (a s)) := by
    funext s
    simpa only [h, one_smul] using hOut s
  have hLowerNew : ∀ s, visibleConnectorDet (deriv P s) (W s) < 0 := by
    intro s
    exact neg_pos.mp (hANew s)
  have hUpperNew : ∀ s, visibleConnectorDet (deriv P s + h s • deriv W s) (W s) < 0 := by
    intro s
    simp only [h, one_smul]
    have he := visibleConnector_source_determinant P Gamma W (![s, 1] : Coord)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul] at he
    rw [he]
    exact neg_lt_zero.mpr (hClosed ![s, 1] (by simp) (by simp))
  have hOuterNew : PositiveJordanParametrization Ho
      (fun t => seamComplexCoord.symm (P (L * t) + h (L * t) • W (L * t))) := by
    change PositiveJordanParametrization Ho
      (fun t => seamComplexCoord.symm ((fun s => P s + h s • W s) (L * t)))
    rw [hOutFn]
    exact hOuter
  have hInnerNew : PositiveJordanParametrization Hi
      (fun t => seamComplexCoord.symm (P (L * t))) := by
    simpa only [hIn] using hInner
  have hDisjointNew : Disjoint (range P) (range (fun s => P s + h s • W s)) := by
    rw [hOutFn, hIn]
    exact hDisjoint
  exact visibleConnectorOrdinaryFamilyRawPotential_global hL hP hGamma hW hf
    (contDiff_const (c := (1 : ℝ))) hPL hGammaL hWL hfL
    (fun _ => rfl) (fun _ => zero_lt_one) hval
    hLowerNew hUpperNew hBNew hOuterNew hInnerNew hDisjointNew hcOuter hcInner

end
end TightVer401
