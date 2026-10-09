import TightVer401.PositiveExitConstructionCoordinates
import TightVer401.IdentityBandCentralSupportExtension
import TightVer401.IdentityBandPlanarSupportPotential
import TightVer401.PlanarTrace
import TightVer401.NativeCircleJordan
import TightVer401.CorrugatedSeedEnclosure
import TightVer401.FermiSupportReturnVariation
import TightVer401.FermiSupportPerturbedMean
import TightVer401.FermiPerturbationCollar
import TightVer401.ExitPositiveGraphProfile

/-! Definition-only call contracts for the unproved two-exit application.
Every inverse, exit, perturbation and return below is an OUTPUT. These types
provide no inhabitant and are not hypotheses granting an exit construction. -/
open scoped Manifold
namespace TightVer401
noncomputable section
open Set Filter MeasureTheory OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix

def positiveExitComplexPoint (q : Coord) : ℂ := ⟨q 0, q 1⟩

def positiveExitComplexTrace (p : ℝ → Coord) : ℝ → ℂ :=
  positiveExitComplexPoint ∘ p

def positiveExitJordanRange (p : ℝ → Coord) : Set Schoenflies.Plane :=
  range (jordanComplexCoordinates.symm ∘ positiveExitComplexTrace p)

def positiveExitInside (p : ℝ → Coord) : Set Coord :=
  {q | jordanComplexCoordinates.symm (positiveExitComplexPoint q) ∈
    Schoenflies.inside (positiveExitJordanRange p)}

def positiveExitFlowTrace {T w delta : ℝ} (d : PeriodicRuledFrame T)
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) Coord)
    (hbalance : (∫ s in 0..T, ruledPeriodCoefficient d.k d.τ s) = 0)
    (hinside : ∀ v ∈ Ioo (0 : ℝ) delta, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 v t ∈ Ioo 0 w)
    (v : ℝ) (hv : v ∈ Ioo (0 : ℝ) delta) (s : ℝ) : Coord :=
  e (identityFlowBandInclusion d hbalance 0 hinside (periodProjection T s, ⟨v, hv⟩))

/-- Ordinary actual source/gradient/value traces. Topology and winding are
explicit conclusions, rather than inferred merely from annulus terminology. -/
structure PositiveExitTrace (G : Coord → ℝ) (U : Set Coord) (L : ℝ) where
  period_pos : 0 < L
  p : ℝ → Coord
  gamma : ℝ → Coord
  p_smooth : ContDiff ℝ ∞ p
  gamma_smooth : ContDiff ℝ ∞ gamma
  p_periodic : Function.Periodic p L
  gamma_periodic : Function.Periodic gamma L
  p_in_domain : MapsTo p univ U
  actual_gradient : gamma = planarGradient G ∘ p
  source_regular : ∀ s, deriv p s ≠ 0
  gradient_regular : ∀ s, deriv gamma s ≠ 0
  source_injective : Function.Injective p_periodic.lift
  gradient_injective : Function.Injective gamma_periodic.lift
  source_jordan : Schoenflies.IsJordanCurve (positiveExitJordanRange p)
  gradient_jordan : Schoenflies.IsJordanCurve (positiveExitJordanRange gamma)
  source_nonzero : ∀ s, p s ≠ 0
  gradient_nonzero : ∀ s, gamma s ≠ 0
  source_turn : HasPositiveArgumentTurn (positiveExitComplexTrace p) L
  gradient_turn : HasPositiveArgumentTurn (positiveExitComplexTrace gamma) L
  source_enclosure : (0 : Coord) ∈ positiveExitInside p
  gradient_enclosure : (0 : Coord) ∈ positiveExitInside gamma
  tangent_pairing : ∀ s, 0 < deriv p s ⬝ᵥ deriv gamma s
  value_smooth : ContDiff ℝ ∞ (G ∘ p)
  value_periodic : Function.Periodic (G ∘ p) L
  value_derivative : ∀ s, deriv (G ∘ p) s = gamma s ⬝ᵥ deriv p s
  zero_action : (∫ s in 0..L, gamma s ⬝ᵥ deriv p s) = 0

/-- The actual local support change and nonlinear returns, tied by support
height to the SAME baseline and changed Cartesian potentials. -/
structure PositiveExitReturn (G Gexit : Coord → ℝ) (U Uexit : Set Coord)
    (sigma xi : ℝ) where
  period : ℝ
  period_pos : 0 < period
  zeta : ℝ → Ambient
  zeta_smooth : ContDiff ℝ ∞ zeta
  zeta_periodic : Function.Periodic zeta period
  unit : ∀ s, inner ℝ (zeta s) (zeta s) = 1
  unit_speed : ∀ s, inner ℝ (deriv zeta s) (deriv zeta s) = 1
  zeta_injective : Function.Injective zeta_periodic.lift
  north : ∀ s, 0 < zeta s 2
  Q : Set Coord
  Q_open : IsOpen Q
  seam_in_Q : ∀ s, (![s, 0] : Coord) ∈ Q
  fermi_north : ∀ q ∈ Q, 0 < fermiNormalMap zeta q 2
  source_in_domains : ∀ q ∈ Q, positiveExitFermiSource zeta q ∈ U ∩ Uexit
  H : Coord → ℝ
  Hexit : Coord → ℝ
  H_smooth : ContDiffOn ℝ ∞ H Q
  Hexit_smooth : ContDiffOn ℝ ∞ Hexit Q
  H_periodic : FermiPeriodic period H
  Hexit_periodic : FermiPeriodic period Hexit
  baseline_height : ∀ q ∈ Q,
    H q = G (positiveExitFermiSource zeta q) / planarWeight (positiveExitFermiSource zeta q)
  changed_height : ∀ q ∈ Q,
    Hexit q = Gexit (positiveExitFermiSource zeta q) / planarWeight (positiveExitFermiSource zeta q)
  rho : ℝ
  rho_pos : 0 < rho
  epsilon : ℝ
  chosen_sign : 0 < epsilon * sigma
  epsilon_small : |epsilon| < xi
  actual_perturbation : EqOn Hexit
    (fermiPerturbedSupport epsilon (normalLoopCurvature zeta) H (fermiExitCutoff rho rho_pos)) Q
  u0 : Coord → ℝ
  V0 : Set Coord
  V0_open : IsOpen V0
  u0_smooth : ContDiffOn ℝ ∞ u0 V0
  u0_image : ∀ q ∈ V0, (![q 0, u0 q] : Coord) ∈ Q
  baseline_ode : ∀ q ∈ V0, coordPartial 0 u0 q =
    fermiSupportAsymptoticSlope (normalLoopCurvature zeta) H ![q 0, u0 q]
  baseline_seam : ∀ s ∈ Icc (0 : ℝ) period,
    (![s, 0] : Coord) ∈ V0 ∧ u0 ![s, 0] = 0
  baseline_initial : (fun x => u0 ![0, x]) =ᶠ[𝓝 (0 : ℝ)] id
  baseline_return : (fun x => u0 ![period, x]) =ᶠ[𝓝 (0 : ℝ)] id
  u : Coord → ℝ
  V : Set Coord
  V_open : IsOpen V
  u_smooth : ContDiffOn ℝ ∞ u V
  u_image : ∀ q ∈ V, (![q 0, u q] : Coord) ∈ Q
  changed_ode : ∀ q ∈ V, coordPartial 0 u q =
    fermiSupportAsymptoticSlope (normalLoopCurvature zeta) Hexit ![q 0, u q]
  changed_seam : ∀ s ∈ Icc (0 : ℝ) period,
    (![s, 0] : Coord) ∈ V ∧ u ![s, 0] = 0
  changed_initial : (fun x => u ![0, x]) =ᶠ[𝓝 (0 : ℝ)] id
  curvature_mass : 0 < ∫ s in 0..period, (normalLoopCurvature zeta s)^2
  return_derivative : HasDerivAt (fun x => u ![period, x])
    (Real.exp (-(epsilon / 2 * ∫ s in 0..period, (normalLoopCurvature zeta s)^2))) 0
  attraction : 0 < epsilon → ∃ b > 0, ∀ x : ℝ, |x| < b →
    (∀ n : ℕ, |((fun y => u ![period, y])^[n]) x| < b) ∧
    Tendsto (fun n : ℕ => ((fun y => u ![period, y])^[n]) x) atTop (𝓝 0)
  repulsion : epsilon < 0 → ∃ b > 0, ∀ x : ℝ, x ≠ 0 → |x| < b →
    ∃ n : ℕ, b ≤ |((fun y => u ![period, y])^[n]) x|
  graph_delta : ℝ
  graph_delta_nonzero : graph_delta ≠ 0
  graph_side : 0 < graph_delta * epsilon
  graph_in_Q : ∀ s, (![s, graph_delta *
    exitPositiveGraphProfile period (fermiSupportSeamSlope (normalLoopCurvature zeta) Hexit) s] : Coord) ∈ Q

/-- Complete two-exit OUTPUT for a specified actual core chart and field. -/
structure PositiveExitConstructionData {T w : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T) (G : Coord → ℝ) (U : Set Coord)
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) Coord)
    (he : e.source = univ) (Y : AddCircle T × Ioo (0 : ℝ) w → Ambient)
    (hbalance : (∫ s in 0..T, ruledPeriodCoefficient d.k d.τ s) = 0)
    {delta : ℝ} (hinside : ∀ v ∈ Ioo (0 : ℝ) delta, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 v t ∈ Ioo 0 w)
    (O : Set Coord) (xi : ℝ) where
  Gexit : Coord → ℝ
  Uexit : Set Coord
  Uexit_open : IsOpen Uexit
  Gexit_smooth : ContDiffOn ℝ ∞ Gexit Uexit
  saddle : ∀ q ∈ Uexit, (planarHessian Gexit q).det < 0
  protected_open : IsOpen O
  protected_in_domain : O ⊆ Uexit
  protected_support : e '' tsupport Y ⊆ O
  protected_equality : EqOn Gexit G O
  change_set : Set Coord
  change_compact : IsCompact change_set
  change_in_baseline : change_set ⊆ U
  change_away : Disjoint change_set O
  change_support : tsupport (Gexit - G) ⊆ change_set
  change_C2_small : ∀ q ∈ change_set,
    ‖(Gexit - G) q‖ + ‖fderiv ℝ (Gexit - G) q‖ +
      ‖fderiv ℝ (fderiv ℝ (Gexit - G)) q‖ < xi
  outer_return : PositiveExitReturn G Gexit U Uexit 1 xi
  inner_return : PositiveExitReturn G Gexit U Uexit (-1) xi
  outer_phase : ℝ → ℝ
  inner_phase : ℝ → ℝ
  outer_phase_smooth : ContDiff ℝ ∞ outer_phase
  inner_phase_smooth : ContDiff ℝ ∞ inner_phase
  outer_phase_increasing : ∀ s, 0 < deriv outer_phase s
  inner_phase_increasing : ∀ s, 0 < deriv inner_phase s
  outer_phase_period : ∀ s, outer_phase (s + outer_return.period) = outer_phase s + T
  inner_phase_period : ∀ s, inner_phase (s + inner_return.period) = inner_phase s + T
  outer_level : ℝ
  inner_level : ℝ
  level_order : 0 < inner_level ∧ inner_level < outer_level ∧ outer_level < delta
  outer_seam_actual : ∀ s, positiveExitFermiSource outer_return.zeta ![s, 0] =
    e (identityFlowBandInclusion d hbalance 0 hinside
      (periodProjection T (outer_phase s), ⟨outer_level, ⟨lt_trans level_order.1 level_order.2.1,
        level_order.2.2⟩⟩))
  inner_seam_actual : ∀ s, positiveExitFermiSource inner_return.zeta ![s, 0] =
    e (identityFlowBandInclusion d hbalance 0 hinside
      (periodProjection T (inner_phase s), ⟨inner_level, ⟨level_order.1,
        lt_trans level_order.2.1 level_order.2.2⟩⟩))
  outer : PositiveExitTrace Gexit Uexit outer_return.period
  inner : PositiveExitTrace Gexit Uexit inner_return.period
  outer_actual_graph : ∀ s, outer.p s = positiveExitFermiSource outer_return.zeta
    ![s, outer_return.graph_delta * exitPositiveGraphProfile outer_return.period
      (fermiSupportSeamSlope (normalLoopCurvature outer_return.zeta) outer_return.Hexit) s]
  inner_actual_graph : ∀ s, inner.p s = positiveExitFermiSource inner_return.zeta
    ![s, inner_return.graph_delta * exitPositiveGraphProfile inner_return.period
      (fermiSupportSeamSlope (normalLoopCurvature inner_return.zeta) inner_return.Hexit) s]
  source_nesting : closure (positiveExitInside inner.p) ⊆ positiveExitInside outer.p
  gradient_nesting : closure (positiveExitInside outer.gamma) ⊆ positiveExitInside inner.gamma
  source_annulus : Set Coord
  source_annulus_eq : source_annulus = positiveExitInside outer.p \ closure (positiveExitInside inner.p)
  gradient_annulus : Set Coord
  gradient_annulus_eq : gradient_annulus = positiveExitInside inner.gamma \ closure (positiveExitInside outer.gamma)
  source_annulus_in_domain : source_annulus ⊆ Uexit
  source_annulus_in_chart : source_annulus ⊆ e.target
  protected_in_annulus : O ⊆ source_annulus
  source_chart : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) 1) Coord
  source_chart_source : source_chart.source = univ
  source_chart_target : source_chart.target = source_annulus
  source_chart_smooth : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Coord) ∞ source_chart
  source_inverse_smooth : ContMDiffOn 𝓘(ℝ, Coord) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
    source_chart.symm source_annulus
  source_closure_chart : (AddCircle T × Icc (0 : ℝ) 1) ≃ₜ ↥(closure source_annulus)
  gradient_chart : OpenPartialHomeomorph Coord Coord
  gradient_chart_source : gradient_chart.source = source_annulus
  gradient_chart_target : gradient_chart.target = gradient_annulus
  actual_gradient_chart : EqOn gradient_chart (planarGradient Gexit) source_annulus
  gradient_chart_smooth : ContDiffOn ℝ ∞ gradient_chart source_annulus
  gradient_inverse_smooth : ContDiffOn ℝ ∞ gradient_chart.symm gradient_annulus
  gradient_closure_chart : ↥(closure source_annulus) ≃ₜ ↥(closure gradient_annulus)
  gradient_closure_actual : ∀ p,
    (gradient_closure_chart p : Coord) = planarGradient Gexit (p : Coord)
  source_boundary_exact : frontier source_annulus = range inner.p ∪ range outer.p
  gradient_boundary_exact : frontier gradient_annulus = range inner.gamma ∪ range outer.gamma
  source_boundaries_disjoint : Disjoint (range inner.p) (range outer.p)
  gradient_boundaries_disjoint : Disjoint (range inner.gamma) (range outer.gamma)
  same_native_compact_support : HasCompactSupport Y
  same_native_nonzero : ∃ p, Y p ≠ 0
  same_bending : IsInfinitesimalBendingOn (planarSupportMap Gexit) (Y ∘ e.symm) source_annulus
  same_support : (Subtype.val : e.target → Coord) '' tsupport (identityBandPlanarRegionField e he Y) =
    e '' tsupport Y
  outer_visibility : ComplexVisiblePair (1 / 4) (positiveExitComplexTrace outer.p)
    (fun s => Complex.I * positiveExitComplexPoint (outer.gamma s))
  inner_visibility : ComplexVisiblePair (4 / 5)
    (corrugatedReverseReflect (positiveExitComplexTrace inner.gamma))
    (fun s => Complex.I * corrugatedReverseReflect (positiveExitComplexTrace inner.p) s)

/-- TYPE of the desired application to ordinary constructed core data.
There is deliberately no theorem inhabiting this definition. The seed root
must instantiate these inputs from its SAME corrected central/core witnesses. -/
def PositiveExitConstructionStatement {T w delta : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T) (G : Coord → ℝ) (U : Set Coord)
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) Coord)
    (he : e.source = univ) (Y : AddCircle T × Ioo (0 : ℝ) w → Ambient)
    (hbalance : (∫ s in 0..T, ruledPeriodCoefficient d.k d.τ s) = 0)
    (hinside : ∀ v ∈ Ioo (0 : ℝ) delta, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 v t ∈ Ioo 0 w) : Prop :=
  0 < w → 0 < delta → delta < w → PrincipalNormalIdentityBand d →
  IdentityBandTwoSidedCollar d w → IsOpen U → ContDiffOn ℝ ∞ G U →
  ContDiffOn ℝ ∞ (identityBandCentralCoordinates d) (identityBandCentralRawDomain w) →
  MapsTo (identityBandCentralCoordinates d) (identityBandCentralRawDomain w) U →
  EqOn (planarSupportMap G ∘ identityBandCentralCoordinates d) (ruledMap d.γ d.E)
    (identityBandCentralRawDomain w) →
  (∀ s, d.τ s < 0) →
  ((e : _ → Coord) = identityBandPlanarSource (d.bandSphereGauss (b := w))) →
  (∀ p, planarSupportMap G (e p) = d.bandMap p) →
  ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Coord) ∞ e →
  ContMDiffOn 𝓘(ℝ, Coord) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞ e.symm e.target →
  IsBandBending d.bandMap Y → HasCompactSupport Y → (∃ p, Y p ≠ 0) →
  e '' tsupport Y ⊆ range (e ∘ identityFlowBandInclusion d hbalance 0 hinside) →
  (∀ v : ℝ, ∀ hv : v ∈ Ioo (0 : ℝ) delta,
    ComplexVisiblePair (1 / 4)
      (positiveExitComplexTrace (positiveExitFlowTrace d e hbalance hinside v hv))
      (fun s => Complex.I * positiveExitComplexPoint
        (planarGradient G (positiveExitFlowTrace d e hbalance hinside v hv s))) ∧
    ComplexVisiblePair (4 / 5)
      (corrugatedReverseReflect (positiveExitComplexTrace
        (planarGradient G ∘ positiveExitFlowTrace d e hbalance hinside v hv)))
      (fun s => Complex.I * corrugatedReverseReflect
        (positiveExitComplexTrace (positiveExitFlowTrace d e hbalance hinside v hv)) s)) →
  ∀ O : Set Coord, IsOpen O → e '' tsupport Y ⊆ O → IsCompact (closure O) →
    closure O ⊆ range (e ∘ identityFlowBandInclusion d hbalance 0 hinside) →
    ∀ xi : ℝ, 0 < xi → Nonempty (PositiveExitConstructionData d G U e he Y hbalance hinside O xi)

end
end TightVer401
