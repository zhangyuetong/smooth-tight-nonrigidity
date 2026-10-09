import TightVer401.VisibleConnectorIncomingParametersActualDelta
import TightVer401.VisibleConnectorIncomingParametersSigns
import TightVer401.VisibleConnectorIncomingParametersCarrier
import TightVer401.VisibleConnectorIncomingParametersRho

/-! One rho is chosen AFTER the fixed-eta family and SAME native inverse.
Actual coefficient, lower-old-Delta, carrier and height margins are produced
before intersection. Only the phase and displaced-terminal thresholds remain
supplied by their separate actual producers. No Gin/raw matching is assumed.
-/
namespace TightVer401
noncomputable section
open Set Function OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Construct ONE compatible rho retaining literal SAME e,a,b,P,G,W. -/
theorem visibleConnectorIncomingParameters_exists_compatible_rho
    {L : ℝ} [hL : Fact (0 < L)] {p : ℝ → Coord}
    (e : OpenPartialHomeomorph (ℝ × (AddCircle L × ℝ)) (ℝ × Coord))
    {Omega : Set (ℝ × ℝ)} {P G W : ℝ × ℝ → Coord} {GinU : Set Coord}
    (hOmega : IsOpen Omega)
    (hP : ContDiffOn ℝ ∞ P Omega) (hG : ContDiffOn ℝ ∞ G Omega)
    (hW : ContDiffOn ℝ ∞ W Omega)
    (hOmegaAxis : ∀ s, (0, s) ∈ Omega)
    (hPL : ∀ rho, Periodic (fun s => P (rho, s)) L)
    (hGL : ∀ rho, Periodic (fun s => G (rho, s)) L)
    (hWL : ∀ rho, Periodic (fun s => W (rho, s)) L)
    (hcentral : ∀ s,
      0 < visibleConnectorA (fun t => P (0, t)) (fun t => W (0, t)) s ∧
      0 < visibleConnectorB (fun t => G (0, t)) (fun t => W (0, t)) s ∧
      0 < visibleConnectorC (fun t => G (0, t)) (fun t => W (0, t)) s)
    (hGinU : IsOpen GinU) (hP0 : ∀ s, P (0, s) ∈ GinU)
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
      (∀ s, 0 < visibleConnectorA (fun t => P (rho, t)) (fun t => W (rho, t)) s ∧
        0 < visibleConnectorB (fun t => G (rho, t)) (fun t => W (rho, t)) s ∧
        0 < visibleConnectorC (fun t => G (rho, t)) (fun t => W (rho, t)) s) ∧
      (∀ s, 0 < visibleConnectorDelta
        (fun t => P (rho, t)) (fun t => G (rho, t)) (fun t => W (rho, t))
        (![visibleConnectorDisplacedRealPhase e p (rho, s),
          (visibleConnectorDisplacedNativeSolution e p (rho, s)).2] : Coord)) ∧
      (∀ s u, (visibleConnectorDisplacedNativeSolution e p (rho, s)).2 ≤ u → u ≤ 0 →
        P (rho, visibleConnectorDisplacedRealPhase e p (rho, s)) +
          u • W (rho, visibleConnectorDisplacedRealPhase e p (rho, s)) ∈ GinU) ∧
      (∀ s, |(visibleConnectorDisplacedNativeSolution e p (rho, s)).2| < r) := by
  obtain ⟨coefficient, hcoefficient, hcoeff⟩ :=
    visibleConnectorIncomingParameters_uniform_actual_coefficient_signs hOmega hP hG hW
      hOmegaAxis hPL hGL hWL hcentral
  obtain ⟨lowerDelta, hlowerDelta, hDelta⟩ :=
    visibleConnectorIncomingParameters_uniform_actual_lower_delta e hOmega hP hG hW
      hOmegaAxis hPL hGL hWL (fun s => (hcentral s).1)
      hD ha hb haxis ha0 hb0 hashift hbL
  obtain ⟨carrier, hcarrier, hsource⟩ :=
    visibleConnectorIncomingParameters_uniform_source_domain hL.out hOmega hP hW
      hOmegaAxis hPL hWL hGinU hP0
  obtain ⟨rho, hρ, hρphase, hρcarrier, hρcoefficient, hρDelta, hρterminal, hsmall⟩ :=
    visibleConnectorIncomingParameters_exists_rho_below_margins e hD hb haxis hb0 hbL
      hphase hcarrier hcoefficient hlowerDelta hterminal (lt_min hr hcarrier)
  have habs : |rho| = rho := abs_of_pos hρ
  have hcoeffRho := hcoeff rho
  have hDeltaRho := hDelta rho
  refine ⟨rho, hρ, hρphase, hρterminal, ?_, ?_, ?_, ?_⟩
  · intro s
    exact hcoeffRho s (by simpa only [habs] using hρcoefficient)
  · intro s
    exact hDeltaRho s (by simpa only [habs] using hρDelta)
  · intro s u hbu hu
    apply hsource rho (visibleConnectorDisplacedRealPhase e p (rho, s)) u
      (by simpa only [habs] using hρcarrier)
    have hbs := hsmall s
    have hbsCarrier : |(visibleConnectorDisplacedNativeSolution e p (rho, s)).2| < carrier :=
      hbs.trans_le (min_le_right _ _)
    rw [abs_of_nonpos hu]
    have hlo := (abs_lt.mp hbsCarrier).1
    linarith
  · intro s
    exact (hsmall s).trans_le (min_le_left _ _)

end
end TightVer401
