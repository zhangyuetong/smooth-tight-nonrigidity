import TightVer401.VisibleConnectorIncomingParametersActualDelta
import TightVer401.VisibleConnectorDisplacedSeamGinFamily

/-! Lower-old-Delta for the literal eta-fixed Gin family, retaining the SAME
native inverse. All coefficient continuity is derived from actual Gin; the
negative original height is not replaced by a positive-height assumption. -/
namespace TightVer401
noncomputable section
open Set Function OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem visibleConnectorIncomingParameters_uniform_Gin_lower_delta
    {L R eta : ℝ} [Fact (0 < L)] {Gin : Coord → ℝ} {U : Set Coord}
    {p w0 gamma : ℝ → Coord}
    (hR : 0 < R) (hU : IsOpen U) (hGin : ContDiffOn ℝ ∞ Gin U)
    (hp : ContDiff ℝ ∞ p) (hw0 : ContDiff ℝ ∞ w0)
    (hpL : Periodic p L) (hw0L : Periodic w0 L)
    (hpU : ∀ s, p s ∈ U) (hgamma : ∀ s, gamma s = planarGradient Gin (p s))
    (hmargin : ∀ s, R < ‖Complex.I * angularDescentComplex (gamma s)‖)
    (hw0same : ∀ s, w0 s = visibleConnectorGinRotatedRuling R eta gamma s)
    (hA0 : ∀ s, 0 < visibleConnectorA p w0 s)
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
      (fun s => (visibleConnectorDisplacedNativeSolution e p (rho, s)).2) L) :
    ∃ delta > 0, ∀ rho s, |rho| < delta →
      0 < visibleConnectorDelta
        (fun t => visibleConnectorGinDisplacedPosition p w0 (rho, t))
        (fun t => visibleConnectorGinDisplacedGradient Gin p w0 (rho, t))
        (fun t => visibleConnectorGinDisplacedRuling Gin R eta p w0 (rho, t))
        (![visibleConnectorDisplacedRealPhase e p (rho, s),
          (visibleConnectorDisplacedNativeSolution e p (rho, s)).2] : Coord) := by
  obtain ⟨hpc, hDU, hgc, hV, hVsub, hVaxis, hW,
    hpcL, hgcL, hWL, _, hgc0, hW0⟩ :=
    visibleConnectorGinDisplacedFamily_properties hR hU hGin hp hw0 hpL hw0L
      hpU hgamma hmargin hw0same
  have hp0 : (fun t => visibleConnectorGinDisplacedPosition p w0 (0, t)) = p := by
    funext t
    simp [visibleConnectorGinDisplacedPosition]
  have hwzero : (fun t => visibleConnectorGinDisplacedRuling Gin R eta p w0 (0, t)) = w0 :=
    funext hW0
  have hAzero : ∀ s, 0 < visibleConnectorA
      (fun t => visibleConnectorGinDisplacedPosition p w0 (0, t))
      (fun t => visibleConnectorGinDisplacedRuling Gin R eta p w0 (0, t)) s := by
    rw [hp0, hwzero]
    exact hA0
  exact visibleConnectorIncomingParameters_uniform_actual_lower_delta e
    hV (hpc.contDiffOn) (hgc.mono hVsub) hW hVaxis hpcL hgcL hWL hAzero
    hD ha hb haxis ha0 hb0 hashift hbL

end
end TightVer401
