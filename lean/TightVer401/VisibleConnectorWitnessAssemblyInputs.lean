import TightVer401.VisibleConnectorContract
import TightVer401.QuadraticRadialFillingBoundaryGerms
import TightVer401.VisibleConnectorSourceInverseGlobal

/-! Ordinary scalar, boundary and germ premises for connector assembly.
There are no inverse, image, collar or connector conclusion fields here.
The actual final scalar and original boundary geometry remain DESC inputs. -/
namespace TightVer401
noncomputable section
open Set Filter MeasureTheory OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix

/-- Ordinary physical terminal boundary facts. Actual value calculus and zero
action are derived below from the supplied actual scalar, rather than assumed. -/
structure VisibleConnectorWitnessAssemblyTerminalFacts (G : Coord → ℝ)
    (U : Set Coord) (L : ℝ) where
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

/-- Build the actual terminal exit trace using scalar differentiation and
the fundamental theorem of calculus for its closed physical period. -/
def visibleConnectorWitnessAssembly_terminal_trace {G : Coord → ℝ}
    {U : Set Coord} {L : ℝ} (hL : 0 < L) (hU : IsOpen U)
    (hG : ContDiffOn ℝ ∞ G U) (T : VisibleConnectorWitnessAssemblyTerminalFacts G U L) :
    PositiveExitTrace G U L where
  period_pos := hL
  p := T.p
  gamma := T.gamma
  p_smooth := T.p_smooth
  gamma_smooth := T.gamma_smooth
  p_periodic := T.p_periodic
  gamma_periodic := T.gamma_periodic
  p_in_domain := T.p_in_domain
  actual_gradient := T.actual_gradient
  source_regular := T.source_regular
  gradient_regular := T.gradient_regular
  source_injective := T.source_injective
  gradient_injective := T.gradient_injective
  source_jordan := T.source_jordan
  gradient_jordan := T.gradient_jordan
  source_nonzero := T.source_nonzero
  gradient_nonzero := T.gradient_nonzero
  source_turn := T.source_turn
  gradient_turn := T.gradient_turn
  source_enclosure := T.source_enclosure
  gradient_enclosure := T.gradient_enclosure
  tangent_pairing := T.tangent_pairing
  value_smooth := contDiffOn_univ.mp (hG.comp T.p_smooth.contDiffOn T.p_in_domain)
  value_periodic := T.p_periodic.comp G
  value_derivative := by
    intro s
    rw [T.actual_gradient]
    exact planarTrace_value_deriv hG hU (T.p_in_domain (mem_univ s))
      (T.p_smooth.differentiable (by simp) s)
  zero_action := by
    rw [T.actual_gradient]
    exact planarTrace_periodic_action_zero hG hU T.p_smooth
      (fun s _ => T.p_in_domain (mem_univ s)) T.p_periodic

/-- A full ordinary incoming open germ implies the actual retained first
jet and positive incoming Hessian pairing for the SAME final scalar. -/
theorem visibleConnectorWitnessAssembly_incoming_germ
    {Gin G : Coord → ℝ} {Uin N : Set Coord} {L R : ℝ} [Fact (0 < L)]
    (D : VisibleConnectorIncomingData Gin Uin L R)
    (hN : IsOpen N) (hpN : range D.incoming.p ⊆ N) (hGerm : EqOn G Gin N) :
    (∀ s, G (D.incoming.p s) = Gin (D.incoming.p s) ∧
      planarGradient G (D.incoming.p s) = D.incoming.gamma s) ∧
    (∀ s, 0 < deriv D.incoming.p s ⬝ᵥ
      (planarHessian G (D.incoming.p s) *ᵥ deriv D.incoming.p s)) := by
  have hgerm (s : ℝ) : G =ᶠ[𝓝 (D.incoming.p s)] Gin :=
    hGerm.eventuallyEq_of_mem (hN.mem_nhds (hpN (mem_range_self s)))
  have hgrad (s : ℝ) : planarGradient Gin (D.incoming.p s) = D.incoming.gamma s := by
    rw [D.incoming.actual_gradient]
    rfl
  constructor
  · intro s
    exact ⟨(hgerm s).eq_of_nhds,
      (quadraticRadialFilling_gradient_eq_of_germ (hgerm s)).trans (hgrad s)⟩
  · intro s
    rw [quadraticRadialFilling_hessian_eq_of_germ (hgerm s)]
    have hd := planarTrace_gradient_deriv D.potential_smooth D.domain_open
      (D.incoming.p_in_domain (mem_univ s))
      (D.incoming.p_smooth.differentiable (by simp) s)
    change deriv (planarGradient Gin ∘ D.incoming.p) s = _ at hd
    rw [← D.incoming.actual_gradient] at hd
    rw [← hd]
    exact D.incoming.tangent_pairing s

/-- Actual ordinary DESC data, with one final scalar/source selection.
All topology premises concern actual physical boundary curves; global charts
and annular images are constructed by the downstream degree producers. -/
structure VisibleConnectorWitnessAssemblyOrdinaryData {Gin : Coord → ℝ}
    {Uin : Set Coord} {L R : ℝ} [Fact (0 < L)]
    (D : VisibleConnectorIncomingData Gin Uin L R) (etaMax : ℝ) where
  eta : ℝ
  eta_pos : 0 < eta
  eta_small : eta < etaMax
  G : Coord → ℝ
  U : Set Coord
  U_open : IsOpen U
  G_smooth : ContDiffOn ℝ ∞ G U
  terminal : VisibleConnectorWitnessAssemblyTerminalFacts G U L
  theta : ℝ → ℝ
  theta_smooth : ContDiff ℝ ∞ theta
  theta_increasing : ∀ s, 0 < deriv theta s
  theta_turn : ∀ s, theta (s + L) = theta s + 2 * Real.pi
  terminal_circle : ∀ s, terminal.gamma s = R • visibleConnectorUnitDirection (theta s)
  terminal_radial_positive : ∀ s, 0 < terminal.p s ⬝ᵥ visibleConnectorUnitDirection (theta s)
  source_nesting : closure (positiveExitInside D.incoming.p) ⊆ positiveExitInside terminal.p
  gradient_nesting : closure (positiveExitInside terminal.gamma) ⊆ positiveExitInside D.incoming.gamma
  source_closure_in_domain : closure (positiveExitInside terminal.p \
    closure (positiveExitInside D.incoming.p)) ⊆ U
  actual_saddle_closed : ∀ q ∈ closure (positiveExitInside terminal.p \
    closure (positiveExitInside D.incoming.p)), (planarHessian G q).det < 0
  incoming_neighborhood : Set Coord
  incoming_neighborhood_open : IsOpen incoming_neighborhood
  incoming_curve_in_neighborhood : range D.incoming.p ⊆ incoming_neighborhood
  incoming_neighborhood_in_domains : incoming_neighborhood ⊆ U ∩ Uin
  incoming_germ_retained : EqOn G Gin incoming_neighborhood
  F : Coord → Coord
  O : Set Coord
  O_open : IsOpen O
  F_smooth : ContDiffOn ℝ ∞ F O
  closed_round_in_domain : {q : Coord | 1 ≤ planarRadius q ∧ planarRadius q ≤ 2} ⊆ O
  F_jacobian_positive : ∀ q : Coord, 1 ≤ planarRadius q → planarRadius q ≤ 2 →
    0 < annularJacobian F q
  source_incoming : ∀ s, F (saddlePolarChart ![1, 2 * Real.pi * s / L]) = D.incoming.p s
  source_terminal : ∀ s, F (saddlePolarChart ![2, 2 * Real.pi * s / L]) = terminal.p s

end
end TightVer401
