import TightVer401.VisibleConnectorIncomingGinFamilyStability

/-! Exact fixed-eta application to GinDisplacedPosition/Gradient/Ruling.
Eta is supplied once by the earlier terminal construction and never selected
again.  One actual small-rho margin gives the entire real visibility circle,
actual smooth periodic curves, strict coefficients, terminal ratio and a
uniform negative-height source extension.  Terminal C1/Jordan stability and
inverse-height smallness must later be intersected with this margin. -/
namespace TightVer401
noncomputable section
open Set Function OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem visibleConnectorIncomingGinFamily_actual_fixed_eta_stability
    {L R eta : ℝ} (hL : 0 < L) (hR : 0 < R)
    {Gin : Coord → ℝ} {GinU : Set Coord} {p w0 gamma : ℝ → Coord}
    (hU : IsOpen GinU) (hGin : ContDiffOn ℝ ∞ Gin GinU)
    (hp : ContDiff ℝ ∞ p) (hw0 : ContDiff ℝ ∞ w0)
    (hpL : Periodic p L) (hw0L : Periodic w0 L)
    (hpU : ∀ s, p s ∈ GinU)
    (hgamma : ∀ s, gamma s = planarGradient Gin (p s))
    (hmargin : ∀ s, R < ‖Complex.I * angularDescentComplex (gamma s)‖)
    (hw0same : ∀ s, w0 s = visibleConnectorGinRotatedRuling R eta gamma s)
    (hcentral : ∀ s, 0 < visibleConnectorA p w0 s ∧
      0 < visibleConnectorB gamma w0 s ∧ 0 < visibleConnectorC gamma w0 s) :
    ∃ delta > 0, ∃ r > 0, ∀ rho, |rho| < delta →
      let pc := fun s => visibleConnectorGinDisplacedPosition p w0 (rho, s)
      let gc := fun s => visibleConnectorGinDisplacedGradient Gin p w0 (rho, s)
      let wc := fun s => visibleConnectorGinDisplacedRuling Gin R eta p w0 (rho, s)
      let tc := visibleConnectorActualTerminalHeight pc gc wc
      (∀ s, (rho, s) ∈ visibleConnectorGinDisplacedVisibilityDomain Gin GinU R p w0) ∧
      ContDiff ℝ ∞ pc ∧ ContDiff ℝ ∞ gc ∧ ContDiff ℝ ∞ wc ∧
      Periodic pc L ∧ Periodic gc L ∧ Periodic wc L ∧
      ContDiff ℝ ∞ tc ∧ Periodic tc L ∧
      (∀ s, 0 < visibleConnectorA pc wc s ∧ 0 < visibleConnectorB gc wc s ∧
        0 < visibleConnectorC gc wc s ∧ 0 < tc s ∧
        ∀ u ∈ Icc (-r) (tc s), 0 < visibleConnectorDelta pc gc wc ![s, u]) := by
  obtain ⟨hP, _, hG, hOmega, hOmegaSub, haxis, hW, hPperiod, hGperiod,
    hWperiod, hOmegaL, hGzero, hWzero⟩ :=
    visibleConnectorGinDisplacedFamily_properties hR hU hGin hp hw0 hpL hw0L
      hpU hgamma hmargin hw0same
  have hPzero : (fun s => visibleConnectorGinDisplacedPosition p w0 (0, s)) = p := by
    funext s
    simp only [visibleConnectorGinDisplacedPosition, zero_smul, add_zero]
  have hGzeroEq : (fun s => visibleConnectorGinDisplacedGradient Gin p w0 (0, s)) = gamma :=
    funext hGzero
  have hWzeroEq : (fun s => visibleConnectorGinDisplacedRuling Gin R eta p w0 (0, s)) = w0 :=
    funext hWzero
  have hcentralActual (s : ℝ) :
      0 < visibleConnectorA (fun x => visibleConnectorGinDisplacedPosition p w0 (0, x))
        (fun x => visibleConnectorGinDisplacedRuling Gin R eta p w0 (0, x)) s ∧
      0 < visibleConnectorB (fun x => visibleConnectorGinDisplacedGradient Gin p w0 (0, x))
        (fun x => visibleConnectorGinDisplacedRuling Gin R eta p w0 (0, x)) s ∧
      0 < visibleConnectorC (fun x => visibleConnectorGinDisplacedGradient Gin p w0 (0, x))
        (fun x => visibleConnectorGinDisplacedRuling Gin R eta p w0 (0, x)) s := by
    simpa only [hPzero, hGzeroEq, hWzeroEq] using hcentral s
  exact visibleConnectorIncomingGinFamily_exists_coefficient_stability hL hOmega
    hP.contDiffOn (hG.mono hOmegaSub) hW haxis hOmegaL hPperiod hGperiod hWperiod hcentralActual

end
end TightVer401
