import TightVer401.PositiveExitConstructionContract
import TightVer401.PolarSupportGerm

/-! Definition-only ordinary call contracts for the unproved connector.
These structures have no construction theorem. Their annular inverses and
terminal positivity are OUTPUTS, never an assumed connector package. -/
open scoped Manifold
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix

def visibleConnectorUnitDirection (theta : ℝ) : Coord :=
  ![Real.cos theta, Real.sin theta]

/-- Actual incoming exit trace and potential germ. This can be populated by
the outer exit or the correctly reflected/reversed dual inner exit. -/
structure VisibleConnectorIncomingData (Gin : Coord → ℝ) (Uin : Set Coord)
    (L R : ℝ) [Fact (0 < L)] where
  incoming : PositiveExitTrace Gin Uin L
  radius_pos : 0 < R
  domain_open : IsOpen Uin
  potential_smooth : ContDiffOn ℝ ∞ Gin Uin
  potential_saddle : ∀ q ∈ Uin, (planarHessian Gin q).det < 0
  delta : ℝ → ℂ
  actual_delta : delta = fun s => Complex.I * positiveExitComplexPoint (incoming.gamma s)
  visibility : ComplexVisiblePair R (positiveExitComplexTrace incoming.p) delta

/-- Actual annular potential, maps and ordinary boundary/degree data. All
global inverse and nesting claims are conclusions of the future construction. -/
structure VisibleConnectorConstructionData {Gin : Coord → ℝ} {Uin : Set Coord}
    {L R : ℝ} [Fact (0 < L)] (D : VisibleConnectorIncomingData Gin Uin L R) (etaMax : ℝ) where
  eta : ℝ
  eta_pos : 0 < eta
  eta_small : eta < etaMax
  G : Coord → ℝ
  U : Set Coord
  U_open : IsOpen U
  G_smooth : ContDiffOn ℝ ∞ G U
  source_annulus : Set Coord
  gradient_annulus : Set Coord
  source_annulus_open : IsOpen source_annulus
  gradient_annulus_open : IsOpen gradient_annulus
  source_closure_compact : IsCompact (closure source_annulus)
  gradient_closure_compact : IsCompact (closure gradient_annulus)
  source_closure_in_domain : closure source_annulus ⊆ U
  actual_saddle : ∀ q ∈ source_annulus, (planarHessian G q).det < 0
  terminal : PositiveExitTrace G U L
  incoming_trace_retained : ∀ s,
    G (D.incoming.p s) = Gin (D.incoming.p s) ∧
      planarGradient G (D.incoming.p s) = D.incoming.gamma s
  incoming_neighborhood : Set Coord
  incoming_neighborhood_open : IsOpen incoming_neighborhood
  incoming_curve_in_neighborhood : range D.incoming.p ⊆ incoming_neighborhood
  incoming_neighborhood_in_domains : incoming_neighborhood ⊆ U ∩ Uin
  incoming_germ_retained : EqOn G Gin incoming_neighborhood
  incoming_positive_pairing : ∀ s, 0 < deriv D.incoming.p s ⬝ᵥ
    (planarHessian G (D.incoming.p s) *ᵥ deriv D.incoming.p s)
  theta : ℝ → ℝ
  theta_smooth : ContDiff ℝ ∞ theta
  theta_increasing : ∀ s, 0 < deriv theta s
  theta_turn : ∀ s, theta (s + L) = theta s + 2 * Real.pi
  terminal_circle : ∀ s, terminal.gamma s = R • visibleConnectorUnitDirection (theta s)
  terminal_radial_positive : ∀ s, 0 < terminal.p s ⬝ᵥ visibleConnectorUnitDirection (theta s)
  source_nesting : closure (positiveExitInside D.incoming.p) ⊆ positiveExitInside terminal.p
  gradient_nesting : closure (positiveExitInside terminal.gamma) ⊆ positiveExitInside D.incoming.gamma
  source_annulus_eq : source_annulus =
    positiveExitInside terminal.p \ closure (positiveExitInside D.incoming.p)
  gradient_annulus_eq : gradient_annulus =
    positiveExitInside D.incoming.gamma \ closure (positiveExitInside terminal.gamma)
  raw_source : Coord → Coord
  raw_source_smooth : ContDiffOn ℝ ∞ raw_source {q | q 1 ∈ Ioo (0 : ℝ) 1}
  raw_source_periodic : ∀ s t, raw_source (![s + L, t] : Coord) = raw_source (![s, t] : Coord)
  raw_source_incoming : ∀ s, raw_source (![s, 0] : Coord) = D.incoming.p s
  raw_source_terminal : ∀ s, raw_source (![s, 1] : Coord) = terminal.p s
  raw_source_interior : MapsTo raw_source {q | q 1 ∈ Ioo (0 : ℝ) 1} source_annulus
  source_degree_sign : ∀ q, q 1 ∈ Ioo (0 : ℝ) 1 →
    (positiveExitJacobian raw_source q).det < 0
  gradient_degree_sign : ∀ q, q 1 ∈ Ioo (0 : ℝ) 1 →
    (positiveExitJacobian (planarGradient G ∘ raw_source) q).det > 0
  native_source : AddCircle L × Icc (0 : ℝ) 1 → Coord
  native_source_continuous : Continuous native_source
  native_source_actual : ∀ s (t : Icc (0 : ℝ) 1),
    native_source (periodProjection L s, t) = raw_source (![s, (t : ℝ)] : Coord)
  source_closure_chart : (AddCircle L × Icc (0 : ℝ) 1) ≃ₜ ↥(closure source_annulus)
  source_closure_chart_actual : ∀ p, (source_closure_chart p : Coord) = native_source p
  source_chart : OpenPartialHomeomorph (AddCircle L × Ioo (0 : ℝ) 1) Coord
  source_chart_source : source_chart.source = univ
  source_chart_target : source_chart.target = source_annulus
  source_chart_actual : ∀ p, source_chart p = native_source
    (p.1, ⟨(p.2 : ℝ), ⟨p.2.property.1.le, p.2.property.2.le⟩⟩)
  source_chart_smooth : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Coord) ∞ source_chart
  source_inverse_smooth : ContMDiffOn 𝓘(ℝ, Coord) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
    source_chart.symm source_annulus
  gradient_chart : OpenPartialHomeomorph Coord Coord
  gradient_chart_source : gradient_chart.source = source_annulus
  gradient_chart_target : gradient_chart.target = gradient_annulus
  gradient_chart_actual : EqOn gradient_chart (planarGradient G) source_annulus
  gradient_chart_smooth : ContDiffOn ℝ ∞ gradient_chart source_annulus
  gradient_inverse_smooth : ContDiffOn ℝ ∞ gradient_chart.symm gradient_annulus
  /-- The same actual gradient extends across the terminal seam as a smooth
  invertible map on open sets, including the entire terminal gradient circle. -/
  terminal_source_collar : Set Coord
  terminal_gradient_collar : Set Coord
  terminal_source_collar_open : IsOpen terminal_source_collar
  terminal_gradient_collar_open : IsOpen terminal_gradient_collar
  terminal_source_in_domain : terminal_source_collar ⊆ U
  terminal_source_in_collar : range terminal.p ⊆ terminal_source_collar
  terminal_gradient_in_collar : range terminal.gamma ⊆ terminal_gradient_collar
  terminal_circle_in_collar : {y : Coord | planarRadius y = R} ⊆ terminal_gradient_collar
  terminal_saddle : ∀ q ∈ terminal_source_collar, (planarHessian G q).det < 0
  terminal_gradient_chart : OpenPartialHomeomorph Coord Coord
  terminal_gradient_chart_source : terminal_gradient_chart.source = terminal_source_collar
  terminal_gradient_chart_target : terminal_gradient_chart.target = terminal_gradient_collar
  terminal_gradient_chart_actual : EqOn terminal_gradient_chart (planarGradient G)
    terminal_source_collar
  terminal_gradient_chart_smooth : ContDiffOn ℝ ∞ terminal_gradient_chart terminal_source_collar
  terminal_gradient_inverse_smooth : ContDiffOn ℝ ∞ terminal_gradient_chart.symm
    terminal_gradient_collar
  terminal_chart_matches : EqOn terminal_gradient_chart gradient_chart
    (terminal_source_collar ∩ source_annulus)
  terminal_inverse_matches : EqOn terminal_gradient_chart.symm gradient_chart.symm
    (terminal_gradient_collar ∩ gradient_annulus)
  gradient_closure_chart : ↥(closure source_annulus) ≃ₜ ↥(closure gradient_annulus)
  gradient_closure_chart_actual : ∀ p,
    (gradient_closure_chart p : Coord) = planarGradient G (p : Coord)
  source_boundary_exact : frontier source_annulus = range D.incoming.p ∪ range terminal.p
  gradient_boundary_exact : frontier gradient_annulus = range D.incoming.gamma ∪ range terminal.gamma
  source_boundaries_disjoint : Disjoint (range D.incoming.p) (range terminal.p)
  gradient_boundaries_disjoint : Disjoint (range D.incoming.gamma) (range terminal.gamma)
  source_boundary_injective : ∀ b : Bool,
    Function.Injective (if b then terminal.p_periodic.lift else D.incoming.p_periodic.lift)
  gradient_boundary_injective : ∀ b : Bool,
    Function.Injective (if b then terminal.gamma_periodic.lift else D.incoming.gamma_periodic.lift)

/-- TYPE of the desired ordinary construction. `D` consists only of actual
incoming trace/germ/action/visibility facts supplied by the exit application.
There is no theorem claiming this type is inhabited. -/
def VisibleConnectorConstructionStatement {Gin : Coord → ℝ} {Uin : Set Coord}
    {L R : ℝ} [Fact (0 < L)] (D : VisibleConnectorIncomingData Gin Uin L R) : Prop :=
  ∀ etaMax : ℝ, 0 < etaMax → Nonempty (VisibleConnectorConstructionData D etaMax)

end
end TightVer401
