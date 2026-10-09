import TightVer401.VisibleConnectorIncomingParametersHeight

/-! The second, rho, selection retains the supplied SAME native inverse.
Carrier, coefficient-extension and displaced-terminal thresholds must come
from their actual producers. This arithmetic intersection does not certify
those missing geometric producers or a Gin/source match.
-/
namespace TightVer401
noncomputable section
open Set Function OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

/-- After eta and its displaced inverse are fixed, choose a positive rho below
all supplied actual margins and the CONSTRUCTED uniform inverse-height margin.
No new inverse, ruling, eta, Cartesian E or matching germ is selected. -/
theorem visibleConnectorIncomingParameters_exists_rho_below_margins
    {L : ℝ} [Fact (0 < L)] {p : ℝ → Coord}
    (e : OpenPartialHomeomorph (ℝ × (AddCircle L × ℝ)) (ℝ × Coord))
    (hD : IsOpen (visibleConnectorDisplacedRealPhaseDomain e p))
    (hb : ContDiffOn ℝ ∞
      (fun z => (visibleConnectorDisplacedNativeSolution e p z).2)
      (visibleConnectorDisplacedRealPhaseDomain e p))
    (haxis : ∀ s, (0, s) ∈ visibleConnectorDisplacedRealPhaseDomain e p)
    (hb0 : ∀ s, (visibleConnectorDisplacedNativeSolution e p (0, s)).2 = 0)
    (hbL : ∀ rho, Periodic
      (fun s => (visibleConnectorDisplacedNativeSolution e p (rho, s)).2) L)
    {phase carrier coefficient lowerDelta terminal r : ℝ}
    (hphase : 0 < phase) (hcarrier : 0 < carrier)
    (hcoefficient : 0 < coefficient) (hlowerDelta : 0 < lowerDelta)
    (hterminal : 0 < terminal) (hr : 0 < r) :
    ∃ rho > 0, rho < phase ∧ rho < carrier ∧ rho < coefficient ∧ rho < lowerDelta ∧ rho < terminal ∧
      (∀ s, |(visibleConnectorDisplacedNativeSolution e p (rho, s)).2| < r) := by
  obtain ⟨height, hheight, hsmall⟩ :=
    visibleConnectorIncomingParameters_uniform_height_small e hD hb haxis hb0 hbL hr
  let eps := min phase (min carrier (min coefficient (min lowerDelta (min terminal height))))
  have heps : 0 < eps := lt_min hphase
    (lt_min hcarrier (lt_min hcoefficient (lt_min hlowerDelta (lt_min hterminal hheight))))
  let rho := eps / 2
  have hρ : 0 < rho := half_pos heps
  have hρeps : rho < eps := half_lt_self heps
  have hρphase : rho < phase := hρeps.trans_le (min_le_left _ _)
  have hrest := hρeps.trans_le (min_le_right phase (min carrier (min coefficient (min lowerDelta (min terminal height)))))
  have hρcarrier : rho < carrier := hrest.trans_le (min_le_left _ _)
  have hrest2 := hrest.trans_le (min_le_right carrier (min coefficient (min lowerDelta (min terminal height))))
  have hρcoefficient : rho < coefficient := hrest2.trans_le (min_le_left _ _)
  have hrest3 := hrest2.trans_le (min_le_right coefficient (min lowerDelta (min terminal height)))
  have hρlowerDelta : rho < lowerDelta := hrest3.trans_le (min_le_left _ _)
  have hrest4 := hrest3.trans_le (min_le_right lowerDelta (min terminal height))
  have hρterminal : rho < terminal := hrest4.trans_le (min_le_left _ _)
  have hρheight : rho < height := hrest4.trans_le (min_le_right _ _)
  refine ⟨rho, hρ, hρphase, hρcarrier, hρcoefficient, hρlowerDelta, hρterminal, ?_⟩
  intro s
  exact hsmall rho s (by simpa only [abs_of_pos hρ] using hρheight)

end
end TightVer401


