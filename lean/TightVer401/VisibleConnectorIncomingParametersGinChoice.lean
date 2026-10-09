import TightVer401.VisibleConnectorIncomingParametersCompatible
import TightVer401.VisibleConnectorDisplacedSeamGinFamily

/-! Actual compatible parameter choice for the literal fixed-eta Gin family.
The source, gradient and ruling are never independent family witnesses.
Only phase and displaced-terminal bounds remain supplied by actual producers;
carrier, coefficients, old lower Delta and height margins are constructed.
-/
namespace TightVer401
noncomputable section
open Set Function OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Choose one rho for the SAME actual eta-dependent Gin family and native e. -/
theorem visibleConnectorIncomingParameters_exists_Gin_compatible_rho
    {L R eta : ℝ} [Fact (0 < L)] {Gin : Coord → ℝ} {U : Set Coord}
    {p w0 gamma : ℝ → Coord}
    (hR : 0 < R) (hU : IsOpen U) (hGin : ContDiffOn ℝ ∞ Gin U)
    (hp : ContDiff ℝ ∞ p) (hw0 : ContDiff ℝ ∞ w0)
    (hpL : Periodic p L) (hw0L : Periodic w0 L)
    (hpU : ∀ s, p s ∈ U) (hgamma : ∀ s, gamma s = planarGradient Gin (p s))
    (hmargin : ∀ s, R < ‖Complex.I * angularDescentComplex (gamma s)‖)
    (hw0same : ∀ s, w0 s = visibleConnectorGinRotatedRuling R eta gamma s)
    (hcentral : ∀ s, 0 < visibleConnectorA p w0 s ∧
      0 < visibleConnectorB gamma w0 s ∧ 0 < visibleConnectorC gamma w0 s)
    (e : OpenPartialHomeomorph (ℝ × (AddCircle L × ℝ)) (ℝ × Coord))
    (hD : IsOpen (visibleConnectorDisplacedRealPhaseDomain e p))
    (ha : ContDiffOn ℝ ∞ (visibleConnectorDisplacedRealPhase e p)
      (visibleConnectorDisplacedRealPhaseDomain e p))
    (hb : ContDiffOn ℝ ∞
      (fun z => (visibleConnectorDisplacedNativeSolution e p z).2)
      (visibleConnectorDisplacedRealPhaseDomain e p))
    (haxis : ∀ s, (0, s) ∈ visibleConnectorDisplacedRealPhaseDomain e p)
    (ha0 : ∀ s, visibleConnectorDisplacedRealPhase e p (0, s) = s)
    (hb0 : ∀ s, (visibleConnectorDisplacedNativeSolution e p (0, s)).2 = 0)
    (hashift : ∀ rho s, visibleConnectorDisplacedRealPhase e p (rho, s + L) =
      visibleConnectorDisplacedRealPhase e p (rho, s) + L)
    (hbL : ∀ rho, Periodic
      (fun s => (visibleConnectorDisplacedNativeSolution e p (rho, s)).2) L)
    {phase terminal r : ℝ}
    (hphase : 0 < phase) (hterminal : 0 < terminal) (hr : 0 < r) :
    ∃ rho > 0, rho < phase ∧ rho < terminal ∧
      let pc := fun t => visibleConnectorGinDisplacedPosition p w0 (rho, t)
      let gc := fun t => visibleConnectorGinDisplacedGradient Gin p w0 (rho, t)
      let wc := fun t => visibleConnectorGinDisplacedRuling Gin R eta p w0 (rho, t)
      (∀ s, 0 < visibleConnectorA pc wc s ∧
        0 < visibleConnectorB gc wc s ∧ 0 < visibleConnectorC gc wc s) ∧
      (∀ s, 0 < visibleConnectorDelta pc gc wc
        (![visibleConnectorDisplacedRealPhase e p (rho, s),
          (visibleConnectorDisplacedNativeSolution e p (rho, s)).2] : Coord)) ∧
      (∀ s u, (visibleConnectorDisplacedNativeSolution e p (rho, s)).2 ≤ u → u ≤ 0 →
        pc (visibleConnectorDisplacedRealPhase e p (rho, s)) +
          u • wc (visibleConnectorDisplacedRealPhase e p (rho, s)) ∈ U) ∧
      (∀ s, |(visibleConnectorDisplacedNativeSolution e p (rho, s)).2| < r) := by
  obtain ⟨hpc, _, hgc, hV, hVsub, hVaxis, hW,
    hpcL, hgcL, hWL, _, hgc0, hW0⟩ :=
    visibleConnectorGinDisplacedFamily_properties hR hU hGin hp hw0 hpL hw0L
      hpU hgamma hmargin hw0same
  have hp0 : (fun t => visibleConnectorGinDisplacedPosition p w0 (0, t)) = p := by
    funext t
    simp [visibleConnectorGinDisplacedPosition]
  have hgzero : (fun t => visibleConnectorGinDisplacedGradient Gin p w0 (0, t)) = gamma :=
    funext hgc0
  have hwzero : (fun t => visibleConnectorGinDisplacedRuling Gin R eta p w0 (0, t)) = w0 :=
    funext hW0
  have hcentralActual : ∀ s,
      0 < visibleConnectorA
        (fun t => visibleConnectorGinDisplacedPosition p w0 (0, t))
        (fun t => visibleConnectorGinDisplacedRuling Gin R eta p w0 (0, t)) s ∧
      0 < visibleConnectorB
        (fun t => visibleConnectorGinDisplacedGradient Gin p w0 (0, t))
        (fun t => visibleConnectorGinDisplacedRuling Gin R eta p w0 (0, t)) s ∧
      0 < visibleConnectorC
        (fun t => visibleConnectorGinDisplacedGradient Gin p w0 (0, t))
        (fun t => visibleConnectorGinDisplacedRuling Gin R eta p w0 (0, t)) s := by
    rw [hp0, hgzero, hwzero]
    exact hcentral
  have hpc0U : ∀ s, visibleConnectorGinDisplacedPosition p w0 (0, s) ∈ U := by
    intro s
    have he := congrFun hp0 s
    rw [he]
    exact hpU s
  exact visibleConnectorIncomingParameters_exists_compatible_rho e hV
    hpc.contDiffOn (hgc.mono hVsub) hW hVaxis hpcL hgcL hWL
    hcentralActual hU hpc0U hD ha hb haxis ha0 hb0 hashift hbL hphase hterminal hr

end
end TightVer401
