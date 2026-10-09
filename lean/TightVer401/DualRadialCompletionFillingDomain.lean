import TightVer401.DualRadialCompletionTraceInside
import TightVer401.PlanarLegendre
import TightVer401.DualRadialCompletionPhase
import TightVer401.VisibleConnectorContract
import TightVer401.QuadraticRadialFillingBoundaryGerms
import TightVer401.QuadraticRadialFillingBoundaryRadial
import TightVer401.QuadraticRadialFillingGradientJordan
import OAI.Analysis.CircleDomains.Topology.RoundCircleParametrization

/-! The actual connector supplies a filling input domain and, given the
returned circle in that domain, directional boundary disjointness. -/
namespace TightVer401
noncomputable section
open Set Metric OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
open scoped ContDiff Topology Matrix

private theorem fillingDomain_polar (R theta : ℝ) :
    R • visibleConnectorUnitDirection theta = saddlePolarChart ![R,theta] := by
  ext i
  fin_cases i <;> rfl
private theorem fillingDomain_coord_radius (z : ℂ) : planarRadius (seamComplexCoord z) = ‖z‖ := by
  rw [seamComplexCoord_apply]
  simp only [planarRadius, Matrix.cons_val_zero, Matrix.cons_val_one,
    Complex.norm_def, Complex.normSq_apply, pow_two]

private theorem fillingDomain_inverse_norm (p : Coord) : ‖seamComplexCoord.symm p‖ = planarRadius p := by
  rw [← fillingDomain_coord_radius, seamComplexCoord.apply_symm_apply]

private theorem fillingDomain_coord_point (p : Coord) : seamComplexCoord (positiveExitComplexPoint p) = p := by
  ext i
  fin_cases i <;> rfl

private theorem fillingDomain_coord_ball (R : ℝ) :
    seamComplexCoord '' ball (0 : ℂ) R = {p : Coord | planarRadius p < R} := by
  ext p
  constructor
  · rintro ⟨z, hz, rfl⟩
    change planarRadius (seamComplexCoord z) < R
    rw [fillingDomain_coord_radius]
    simpa only [mem_ball, dist_zero_right] using hz
  · intro hp
    change planarRadius p < R at hp
    refine ⟨seamComplexCoord.symm p, ?_, seamComplexCoord.apply_symm_apply p⟩
    simpa only [mem_ball, dist_zero_right, fillingDomain_inverse_norm] using hp

private theorem fillingDomain_coord_closedBall (R : ℝ) :
    seamComplexCoord '' closedBall (0 : ℂ) R = {p : Coord | planarRadius p ≤ R} := by
  ext p
  constructor
  · rintro ⟨z, hz, rfl⟩
    change planarRadius (seamComplexCoord z) ≤ R
    rw [fillingDomain_coord_radius]
    simpa only [mem_closedBall, dist_zero_right] using hz
  · intro hp
    change planarRadius p ≤ R at hp
    refine ⟨seamComplexCoord.symm p, ?_, seamComplexCoord.apply_symm_apply p⟩
    simpa only [mem_closedBall, dist_zero_right, fillingDomain_inverse_norm] using hp

section Connector
variable {Gin : Coord → ℝ} {Uin : Set Coord} {L R etaMax : ℝ} [Fact (0 < L)]
variable {D : VisibleConnectorIncomingData Gin Uin L R}

/-- The actual inverse collar, restricted to the incoming gradient disk. -/
def dualRadialCompletionFillingDomain (C : VisibleConnectorConstructionData D etaMax)
    (eC : OpenPartialHomeomorph Coord Coord) : Set Coord :=
  eC.target ∩ positiveExitInside D.incoming.gamma

private theorem fillingDomain_phase_surjective (C : VisibleConnectorConstructionData D etaMax) :
    Function.Surjective C.theta :=
  dualRadialCompletion_phase_surjective C.theta_smooth.continuous
    (strictMono_of_deriv_pos C.theta_increasing) (Fact.out : 0 < L) C.theta_turn

private theorem fillingDomain_terminal_range (C : VisibleConnectorConstructionData D etaMax) :
    range (positiveExitComplexTrace C.terminal.gamma) =
      roundDiskChart R D.radius_pos '' sphere (0 : ℂ) 1 := by
  have hRound : roundDiskChart R D.radius_pos '' sphere (0 : ℂ) 1 = sphere (0 : ℂ) R := by
    rw [← frontier_jordanInterior, roundDiskChart_interior, frontier_ball _ D.radius_pos.ne']
  rw [hRound]
  ext z
  constructor
  · rintro ⟨s, rfl⟩
    rw [mem_sphere, dist_zero_right]
    change ‖positiveExitComplexPoint (C.terminal.gamma s)‖ = R
    rw [← fillingDomain_coord_radius, fillingDomain_coord_point, C.terminal_circle]
    change planarRadius (saddlePolarChart ![R, C.theta s]) = R
    exact angularDescent_radius_polar (show (0 : ℝ) < (![R, C.theta s] : Coord) 0 from D.radius_pos)
  · intro hz
    have hr : planarRadius (seamComplexCoord z) = R := by
      rw [fillingDomain_coord_radius]
      simpa only [mem_sphere, dist_zero_right] using hz
    obtain ⟨theta, hPolar⟩ := quadraticRadialFilling_radiusLevel_exists_polar D.radius_pos hr
    obtain ⟨s, hs⟩ := fillingDomain_phase_surjective C theta
    refine ⟨s, ?_⟩
    apply seamComplexCoord.injective
    change seamComplexCoord (positiveExitComplexPoint (C.terminal.gamma s)) = seamComplexCoord z
    rw [fillingDomain_coord_point, C.terminal_circle, fillingDomain_polar]
    change saddlePolarChart ![R, C.theta s] = seamComplexCoord z
    rw [hs]
    exact hPolar

/-- The actual terminal phase circle bounds exactly the positive-radius ball. -/
theorem dualRadialCompletionFillingDomain_terminal_inside (C : VisibleConnectorConstructionData D etaMax) :
    positiveExitInside C.terminal.gamma = {p : Coord | planarRadius p < R} := by
  have h := dualRadialCompletionTraceInside_eq_of_range (fillingDomain_terminal_range C)
    C.terminal.gradient_jordan
  change positiveExitInside C.terminal.gamma =
    seamComplexCoord '' jordanInterior (roundDiskChart R D.radius_pos) at h
  rw [roundDiskChart_interior, fillingDomain_coord_ball] at h
  exact h

/-- Its actual closed disk is the closed radial ball. -/
theorem dualRadialCompletionFillingDomain_terminal_closure (C : VisibleConnectorConstructionData D etaMax) :
    closure (positiveExitInside C.terminal.gamma) = {p : Coord | planarRadius p ≤ R} := by
  rw [dualRadialCompletionFillingDomain_terminal_inside C, ← fillingDomain_coord_ball,
    ← seamComplexCoord.image_closure, closure_ball _ D.radius_pos.ne']
  exact fillingDomain_coord_closedBall R

/-- A genuine connector inverse collar gives an open filling domain containing
its entire terminal circle; its exterior radial points lie in the old annulus. -/
theorem dualRadialCompletionFillingDomain_properties (C : VisibleConnectorConstructionData D etaMax)
    (eC : OpenPartialHomeomorph Coord Coord)
    (hClosed : closure C.source_annulus ⊆ eC.source)
    (hActual : (eC : Coord → Coord) = planarGradient C.G) :
    IsOpen (dualRadialCompletionFillingDomain C eC) ∧
      {y : Coord | planarRadius y = R} ⊆ dualRadialCompletionFillingDomain C eC ∧
      ∀ y ∈ dualRadialCompletionFillingDomain C eC, R < planarRadius y → y ∈ C.gradient_annulus := by
  have hInsideOpen : IsOpen (positiveExitInside D.incoming.gamma) := by
    have hPoint : positiveExitComplexPoint = (seamComplexCoord.symm : Coord → ℂ) := by
      funext p
      apply Complex.ext <;> rfl
    have hc : Continuous (fun q => jordanComplexCoordinates.symm (positiveExitComplexPoint q)) := by
      rw [hPoint]
      exact jordanComplexCoordinates.symm.continuous.comp seamComplexCoord.symm.continuous
    exact (Schoenflies.isOpen_inside D.incoming.gradient_jordan.isClosed).preimage hc
  refine ⟨eC.open_target.inter hInsideOpen, ?_, ?_⟩
  · intro y hy
    obtain ⟨theta, hPolar⟩ := quadraticRadialFilling_radiusLevel_exists_polar D.radius_pos hy
    obtain ⟨s, hs⟩ := fillingDomain_phase_surjective C theta
    have hTerminal : C.terminal.gamma s = y := by
      rw [C.terminal_circle, fillingDomain_polar]
      change saddlePolarChart ![R, C.theta s] = y
      rw [hs]
      exact hPolar
    have hSourceClosed : C.terminal.p s ∈ closure C.source_annulus := by
      apply frontier_subset_closure
      rw [C.source_boundary_exact]
      exact Or.inr (mem_range_self s)
    have hForward : eC (C.terminal.p s) = y := by
      rw [hActual]
      exact (congrFun C.terminal.actual_gradient s).symm.trans hTerminal
    constructor
    · rw [← hForward]
      exact eC.map_source (hClosed hSourceClosed)
    · apply C.gradient_nesting
      rw [dualRadialCompletionFillingDomain_terminal_closure]
      change planarRadius y ≤ R
      exact (show planarRadius y = R from hy).le
  · intro y hy hr
    rw [C.gradient_annulus_eq]
    refine ⟨hy.2, ?_⟩
    rw [dualRadialCompletionFillingDomain_terminal_closure]
    change ¬planarRadius y ≤ R
    exact not_le.mpr hr

/-- Same filling scalar germs on a returned circle in the actual chosen domain
put its actual new boundary outside the CLOSED incoming source disk. -/
theorem dualRadialCompletionFillingDomain_boundary_disjoint
    (C : VisibleConnectorConstructionData D etaMax) (eC : OpenPartialHomeomorph Coord Coord)
    (hClosed : closure C.source_annulus ⊆ eC.source)
    (hActual : (eC : Coord → Coord) = planarGradient C.G)
    (hG : ContDiffOn ℝ ∞ C.G eC.source) (hi : ContDiffOn ℝ ∞ eC.symm eC.target)
    (hAgreement : EqOn eC.symm C.gradient_chart.symm C.gradient_annulus)
    {H : Coord → ℝ} {S : ℝ} {Gamma : ℂ ≃ₜ ℂ} (hS : R < S)
    (hCircleS : ∀ theta, saddlePolarChart ![S, theta] ∈ dualRadialCompletionFillingDomain C eC)
    (hGerms : ∀ theta, H =ᶠ[𝓝 (saddlePolarChart ![S, theta])] planarLegendre C.G eC)
    (hRange : range (quadraticRadialFillingGradientComplexTrace H S) = Gamma '' sphere (0 : ℂ) 1) :
    Disjoint (closure (positiveExitInside D.incoming.p))
      (seamComplexCoord '' (Gamma '' sphere (0 : ℂ) 1)) := by
  obtain ⟨_, _, hExterior⟩ := dualRadialCompletionFillingDomain_properties C eC hClosed hActual
  have heG : ∀ p ∈ eC.source, eC p = planarGradient C.G p := fun p _ => congrFun hActual p
  have hSource (theta : ℝ) : planarGradient H (saddlePolarChart ![S, theta]) ∈ C.source_annulus := by
    have hy := hCircleS theta
    have hr : planarRadius (saddlePolarChart ![S, theta]) = S :=
      angularDescent_radius_polar (show (0 : ℝ) < (![S, theta] : Coord) 0 from D.radius_pos.trans hS)
    have hAnnulus := hExterior _ hy (by simpa only [hr] using hS)
    rw [quadraticRadialFilling_gradient_eq_of_germ (hGerms theta),
      planarLegendre_gradient eC hG hi heG hy.1, hAgreement hAnnulus]
    rw [← C.gradient_chart_source]
    exact C.gradient_chart.map_target (by simpa only [C.gradient_chart_target] using hAnnulus)
  apply disjoint_left.mpr
  intro p hpOld hpNew
  obtain ⟨z, hz, hzp⟩ := hpNew
  obtain ⟨theta, htheta⟩ := hRange.symm ▸ hz
  have hp : p = planarGradient H (saddlePolarChart ![S, theta]) := by
    calc
      p = seamComplexCoord z := hzp.symm
      _ = seamComplexCoord (quadraticRadialFillingGradientComplexTrace H S theta) := congrArg seamComplexCoord htheta.symm
      _ = planarGradient H (saddlePolarChart ![S, theta]) := by
        change seamComplexCoord (angularDescentComplex (planarGradient H (saddlePolarChart ![S, theta]))) = _
        exact quadraticRadialFillingCoord_complex _
  have hNew := hSource theta
  rw [C.source_annulus_eq] at hNew
  rw [hp] at hpOld
  exact hNew.2 hpOld

/-- The supplied SAME old disk chart turns coordinate disjointness into the
ordinary complex directional input for the Jordan containment adapter. -/
theorem dualRadialCompletionFillingDomain_complex_boundary_disjoint
    (C : VisibleConnectorConstructionData D etaMax) {HOld Gamma : ℂ ≃ₜ ℂ}
    (hOldRange : range (positiveExitComplexTrace D.incoming.p) = HOld '' sphere (0 : ℂ) 1)
    (hDisjoint : Disjoint (closure (positiveExitInside D.incoming.p))
      (seamComplexCoord '' (Gamma '' sphere (0 : ℂ) 1))) :
    Disjoint (closure (HOld '' ball (0 : ℂ) 1)) (frontier (Gamma '' ball (0 : ℂ) 1)) := by
  have hInside := dualRadialCompletionTraceInside_eq_of_range hOldRange D.incoming.source_jordan
  have hClosure : closure (positiveExitInside D.incoming.p) =
      seamComplexCoord '' closure (HOld '' ball (0 : ℂ) 1) := by
    rw [hInside, ← seamComplexCoord.image_closure]
  apply disjoint_left.mpr
  intro z hzOld hzNew
  apply disjoint_left.mp hDisjoint
  · rw [hClosure]
    exact ⟨z, hzOld, rfl⟩
  · refine ⟨z, ?_, rfl⟩
    rwa [← Gamma.image_frontier, frontier_ball _ one_ne_zero] at hzNew

end Connector
end
end TightVer401
