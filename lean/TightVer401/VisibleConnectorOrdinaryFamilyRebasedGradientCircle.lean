import TightVer401.VisibleConnectorOrdinaryFamilyActualChoiceTerminal
import TightVer401.VisibleConnectorOrdinaryFamilyActualChoiceTurn
import TightVer401.VisibleConnectorOrdinaryFamilyRebasedTopology
import TightVer401.VisibleConnectorWitnessAssemblyCircle
import TightVer401.VisibleConnectorWitnessAssemblyTopology
import TightVer401.DualRadialCompletionTraceInside
import OAI.Analysis.CircleDomains.Topology.RoundCircleParametrization

/-! Topology of the SAME actual terminal gradient after its SAME native phase.
The upstream selected-sign and homotopy-turn producers are reused. Its exact
inside is the radius-R disk; no new gradient filling or inverse is chosen. -/
namespace TightVer401
noncomputable section
open Set Function Filter Metric OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

private theorem rebasedGradientCircle_coord_radius (z : ℂ) :
    planarRadius (seamComplexCoord z) = ‖z‖ := by
  rw [seamComplexCoord_apply]
  simp only [planarRadius, Matrix.cons_val_zero, Matrix.cons_val_one,
    Complex.norm_def, Complex.normSq_apply, pow_two]

private theorem rebasedGradientCircle_coord_ball (R : ℝ) :
    seamComplexCoord '' ball (0 : ℂ) R = {p : Coord | planarRadius p < R} := by
  ext p
  constructor
  · rintro ⟨z, hz, rfl⟩
    change planarRadius (seamComplexCoord z) < R
    rw [rebasedGradientCircle_coord_radius]
    simpa only [mem_ball, dist_zero_right] using hz
  · intro hp
    refine ⟨seamComplexCoord.symm p, ?_, seamComplexCoord.apply_symm_apply p⟩
    rw [mem_ball, dist_zero_right, ← rebasedGradientCircle_coord_radius,
      seamComplexCoord.apply_symm_apply]
    exact hp

private theorem rebasedGradientCircle_coord_closedBall (R : ℝ) :
    seamComplexCoord '' closedBall (0 : ℂ) R = {p : Coord | planarRadius p ≤ R} := by
  ext p
  constructor
  · rintro ⟨z, hz, rfl⟩
    change planarRadius (seamComplexCoord z) ≤ R
    rw [rebasedGradientCircle_coord_radius]
    simpa only [mem_closedBall, dist_zero_right] using hz
  · intro hp
    refine ⟨seamComplexCoord.symm p, ?_, seamComplexCoord.apply_symm_apply p⟩
    rw [mem_closedBall, dist_zero_right, ← rebasedGradientCircle_coord_radius,
      seamComplexCoord.apply_symm_apply]
    exact hp

/-- Complete ordinary facts of a SAME actual circle after an increasing
physical phase. All Jordan, lift-injectivity and disk identities are outputs. -/
theorem visibleConnectorOrdinaryFamilyRebasedGradientCircle_actual
    {L R : ℝ} (hL : 0 < L) (hR : 0 < R) {Y : ℝ → Coord} {a : ℝ → ℝ}
    (hY : ContDiff ℝ ∞ Y) (hYL : Periodic Y L)
    (hNorm : ∀ s, ‖positiveExitComplexTrace Y s‖ = R)
    (hTurn : HasPositiveArgumentTurn (positiveExitComplexTrace Y) L)
    (hDet : ∀ s, 0 < visibleConnectorDet (Y s) (deriv Y s))
    (ha : ContDiff ℝ ∞ a) (hap : ∀ s, 0 < deriv a s)
    (hshift : ∀ s, a (s + L) = a s + L) :
    let Ya := fun s => Y (a s)
    ContDiff ℝ ∞ Ya ∧ Periodic Ya L ∧
      (∀ s, deriv Ya s ≠ 0) ∧ InjOn Ya (Ico (0 : ℝ) L) ∧
      (∀ hp : Periodic Ya L, Injective hp.lift) ∧
      Schoenflies.IsJordanCurve (positiveExitJordanRange Ya) ∧
      (∀ s, Ya s ≠ 0) ∧
      HasPositiveArgumentTurn (positiveExitComplexTrace Ya) L ∧
      range Ya = {y : Coord | planarRadius y = R} ∧
      positiveExitInside Ya = {y : Coord | planarRadius y < R} ∧
      closure (positiveExitInside Ya) = {y : Coord | planarRadius y ≤ R} ∧
      (0 : Coord) ∈ positiveExitInside Ya ∧
      ∃ theta : ℝ → ℝ, ContDiff ℝ ∞ theta ∧
        (∀ s, 0 < deriv theta s) ∧
        (∀ s, theta (s + L) = theta s + 2 * Real.pi) ∧
        (∀ s, Ya s = R • visibleConnectorUnitDirection (theta s)) := by
  letI : Fact (0 < L) := ⟨hL⟩
  let Ya := fun s => Y (a s)
  have hne (s : ℝ) : positiveExitComplexTrace Y s ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [hNorm s]
    exact hR.ne'
  have hiY := (visibleConnector_positive_det_turn_jordan hL hY hYL hne hTurn hDet).1
  obtain ⟨hYa, hYaL, hiYa, hneYa, hdetYa, hturnYa, _hrange⟩ :=
    visibleConnectorOrdinaryFamily_rebased_terminal_fields hL hY ha hYL hiY hne hDet hTurn hap hshift
  have hJordan := (visibleConnector_positive_det_turn_jordan hL hYa hYaL hneYa hturnYa hdetYa).2
  have hregular (s : ℝ) : deriv Ya s ≠ 0 := by
    intro he
    have hh := hdetYa s
    rw [he] at hh
    simpa [visibleConnectorDet] using hh
  have hcoordNe (s : ℝ) : Ya s ≠ 0 := by
    intro he
    apply hneYa s
    change positiveExitComplexTrace Ya s = 0
    change positiveExitComplexPoint (Ya s) = 0
    rw [he]
    apply Complex.ext <;> rfl
  have hNormYa (s : ℝ) : ‖positiveExitComplexTrace Ya s‖ = R := hNorm (a s)
  obtain ⟨theta, htheta, hthetaPos, hthetaShift, hRepresentation⟩ :=
    visibleConnectorOrdinaryFamilyTerminalAngle_exists hR hYa hYaL hNormYa hturnYa hdetYa
  have hRange : range Ya = {y : Coord | planarRadius y = R} := by
    have he : Ya = fun s => R • visibleConnectorUnitDirection (theta s) := funext hRepresentation
    change range Ya = {y : Coord | planarRadius y = R}
    rw [he]
    exact visibleConnectorWitnessAssembly_terminal_circle_range hR htheta.continuous hthetaShift
  have hComplexRange : range (positiveExitComplexTrace Ya) =
      roundDiskChart R hR '' sphere (0 : ℂ) 1 := by
    rw [← frontier_jordanInterior, roundDiskChart_interior, frontier_ball _ hR.ne']
    apply Subset.antisymm
    · rintro z ⟨s, rfl⟩
      simpa only [mem_sphere, dist_zero_right] using hNormYa s
    · intro z hz
      have hr : planarRadius (seamComplexCoord z) = R := by
        rw [rebasedGradientCircle_coord_radius]
        simpa only [mem_sphere, dist_zero_right] using hz
      obtain ⟨s, hs⟩ := hRange.symm.subset hr
      refine ⟨s, ?_⟩
      change positiveExitComplexPoint (Ya s) = z
      rw [hs, visibleConnectorWitnessAssemblyTopology_complex_point,
        seamComplexCoord.symm_apply_apply]
  have hInside : positiveExitInside Ya = {y : Coord | planarRadius y < R} := by
    have hh := dualRadialCompletionTraceInside_eq_of_range hComplexRange hJordan
    change positiveExitInside Ya = seamComplexCoord '' jordanInterior (roundDiskChart R hR) at hh
    rw [roundDiskChart_interior, rebasedGradientCircle_coord_ball] at hh
    exact hh
  have hClosure : closure (positiveExitInside Ya) = {y : Coord | planarRadius y ≤ R} := by
    rw [hInside, ← rebasedGradientCircle_coord_ball, ← seamComplexCoord.image_closure,
      closure_ball _ hR.ne']
    exact rebasedGradientCircle_coord_closedBall R
  have hOrigin : (0 : Coord) ∈ positiveExitInside Ya := by
    rw [hInside]
    simpa [planarRadius] using hR
  exact ⟨hYa, hYaL, hregular, hiYa, fun hp => periodicComplexCurve_lift_injective hp hiYa,
    hJordan, hcoordNe, hturnYa, hRange, hInside, hClosure, hOrigin,
    theta, htheta, hthetaPos, hthetaShift, hRepresentation⟩

/-- Apply the circle-topology worker directly to the frozen selected choice.
Y is the literal old endpoint gradient, not a substitute angular curve. -/
theorem visibleConnectorOrdinaryFamilyRebasedGradientCircle_of_choice
    {Gin : Coord → ℝ} {Uin : Set Coord} {L R etaMax : ℝ} [hL : Fact (0 < L)]
    (D : VisibleConnectorIncomingData Gin Uin L R)
    (C : VisibleConnectorIncomingParametersChoice D etaMax) :
    let pc := fun s => visibleConnectorGinDisplacedPosition D.incoming.p C.w0 (C.rho, s)
    let gc := fun s => visibleConnectorGinDisplacedGradient Gin D.incoming.p C.w0 (C.rho, s)
    let wc := fun s => visibleConnectorGinDisplacedRuling Gin R C.etaAngle D.incoming.p C.w0 (C.rho, s)
    let Y := fun s => visibleConnectorGradient pc gc wc ![s, visibleConnectorActualTerminalHeight pc gc wc s]
    let a := fun s => visibleConnectorDisplacedRealPhase C.e D.incoming.p (C.rho, s)
    let Ya := fun s => Y (a s)
    ContDiff ℝ ∞ Y ∧ Periodic Y L ∧
      ContDiff ℝ ∞ Ya ∧ Periodic Ya L ∧
      (∀ s, deriv Ya s ≠ 0) ∧ InjOn Ya (Ico (0 : ℝ) L) ∧
      (∀ hp : Periodic Ya L, Injective hp.lift) ∧
      Schoenflies.IsJordanCurve (positiveExitJordanRange Ya) ∧
      (∀ s, Ya s ≠ 0) ∧
      HasPositiveArgumentTurn (positiveExitComplexTrace Ya) L ∧
      range Ya = {y : Coord | planarRadius y = R} ∧
      positiveExitInside Ya = {y : Coord | planarRadius y < R} ∧
      closure (positiveExitInside Ya) = {y : Coord | planarRadius y ≤ R} ∧
      (0 : Coord) ∈ positiveExitInside Ya ∧
      ∃ theta : ℝ → ℝ, ContDiff ℝ ∞ theta ∧
        (∀ s, 0 < deriv theta s) ∧
        (∀ s, theta (s + L) = theta s + 2 * Real.pi) ∧
        (∀ s, Ya s = R • visibleConnectorUnitDirection (theta s)) := by
  let pc := fun s => visibleConnectorGinDisplacedPosition D.incoming.p C.w0 (C.rho, s)
  let gc := fun s => visibleConnectorGinDisplacedGradient Gin D.incoming.p C.w0 (C.rho, s)
  let wc := fun s => visibleConnectorGinDisplacedRuling Gin R C.etaAngle D.incoming.p C.w0 (C.rho, s)
  let direction := visibleConnectorGinRotatedDirection R C.etaAngle gc
  let Y0 := fun s => -R • visibleConnectorJ (direction s)
  let Y := fun s => visibleConnectorGradient pc gc wc ![s, visibleConnectorActualTerminalHeight pc gc wc s]
  let a := fun s => visibleConnectorDisplacedRealPhase C.e D.incoming.p (C.rho, s)
  obtain ⟨_he, hY0, hJet, hNorm0, hSigns⟩ :=
    visibleConnectorOrdinaryFamilyActualChoiceTerminal_of_choice D C
  have hYY0 : Y = Y0 := funext hJet
  have hY : ContDiff ℝ ∞ Y := hYY0.symm ▸ hY0
  have hgcL : Periodic gc L := by
    intro s
    change planarGradient Gin (D.incoming.p (s + L) + C.rho • C.w0 (s + L)) =
      planarGradient Gin (D.incoming.p s + C.rho • C.w0 s)
    rw [D.incoming.p_periodic s, C.w0_periodic s]
  have hY0L : Periodic Y0 L := by
    intro s
    simp only [Y0, direction, visibleConnectorGinRotatedDirection,
      visibleConnectorTangentDirection, hgcL s]
  have hYL : Periodic Y L := hYY0.symm ▸ hY0L
  have hNorm : ∀ s, ‖positiveExitComplexTrace Y s‖ = R := hYY0.symm ▸ hNorm0
  have hDet : ∀ s, 0 < visibleConnectorDet (Y s) (deriv Y s) := by
    rw [hYY0]
    exact fun s => (hSigns s).2.2
  have hTurn : HasPositiveArgumentTurn (positiveExitComplexTrace Y) L := by
    rw [hYY0]
    exact visibleConnectorOrdinaryFamilyTerminalHomotopyTurn_of_choice D C
  have ha : ContDiff ℝ ∞ a := contDiffOn_univ.mp
    (C.phase_smooth.comp ((contDiff_const (c := C.rho)).prodMk contDiff_id).contDiffOn
      (fun s _ => C.chosen_domain s))
  exact ⟨hY, hYL, visibleConnectorOrdinaryFamilyRebasedGradientCircle_actual hL.out D.radius_pos
    hY hYL hNorm hTurn hDet ha C.phase_positive (C.phase_shift C.rho)⟩

end
end TightVer401



