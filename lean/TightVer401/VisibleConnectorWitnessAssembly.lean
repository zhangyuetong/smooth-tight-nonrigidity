import TightVer401.VisibleConnectorWitnessAssemblyInputs
import TightVer401.VisibleConnectorWitnessAssemblyTopology
import TightVer401.VisibleConnectorWitnessAssemblyOrientation
import TightVer401.VisibleConnectorWitnessAssemblyCircle
import TightVer401.VisibleConnectorGradientInverseApplication

/-! Assemble the canonical witness from ordinary final scalar, original
incoming germ and actual boundary geometry. Every inverse and collar is
constructed by the audited producers for the same supplied F and G. -/
open scoped Manifold
namespace TightVer401
noncomputable section
open Set Function OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

/-- Ordinary final DESC facts construct the canonical connector witness.
There is one source inverse selection and one gradient inverse selection,
both belonging to the supplied final F/G; no independent raw scalar choices. -/
theorem visibleConnectorWitnessAssembly_of_ordinary
    {Gin : Coord → ℝ} {Uin : Set Coord} {L R etaMax : ℝ} [Fact (0 < L)]
    (D : VisibleConnectorIncomingData Gin Uin L R)
    (A : VisibleConnectorWitnessAssemblyOrdinaryData D etaMax) :
    Nonempty (VisibleConnectorConstructionData D etaMax) := by
  have hL : 0 < L := Fact.out
  let T := visibleConnectorWitnessAssembly_terminal_trace hL A.U_open A.G_smooth A.terminal
  obtain ⟨Hi,To,hpi,hgi,_hpi0,_hgi0,_hpiInside,_hgiInside⟩ :=
    visibleConnectorWitnessAssemblyTopology_positive_traces D.incoming
  obtain ⟨Ho,Ti,hpo,hgo,_hpo0,_hgo0,_hpoInside,_hgoInside⟩ :=
    visibleConnectorWitnessAssemblyTopology_positive_traces T
  obtain ⟨hnS,hAnnS,hOpenS,hCompactS,hClosedS,hFrontS,hDisjointS⟩ :=
    visibleConnectorWitnessAssemblyTopology_annulus_geometry hL hpo hpi
      T.source_jordan D.incoming.source_jordan A.source_nesting
  obtain ⟨hnG,hAnnG,hOpenG,hCompactG,hClosedG,hFrontG,hDisjointG⟩ :=
    visibleConnectorWitnessAssemblyTopology_annulus_geometry hL hgi hgo
      D.incoming.gradient_jordan T.gradient_jordan A.gradient_nesting
  have hKU : annularCoordJordanClosure Ho Hi ⊆ A.U := by
    rw [← hClosedS]
    exact A.source_closure_in_domain
  have hNeg : ∀ q ∈ annularCoordJordanClosure Ho Hi, (planarHessian A.G q).det < 0 := by
    rw [← hClosedS]
    exact A.actual_saddle_closed
  have hTraceFo : ∀ t, annularComplexConjugate A.F (unitCircleParam 0 2 t) =
      seamComplexCoord.symm (T.p (L*t)) := by
    intro t
    rw [visibleConnectorWitnessAssembly_complex_physical_boundary hL.ne' A.F 2
      A.terminal.p A.source_terminal,
      visibleConnectorWitnessAssemblyTopology_complex_point]
    rfl
  have hTraceFi : ∀ t, annularComplexConjugate A.F (unitCircleParam 0 1 t) =
      seamComplexCoord.symm (D.incoming.p (L*t)) := by
    intro t
    rw [visibleConnectorWitnessAssembly_complex_physical_boundary hL.ne' A.F 1
      D.incoming.p A.source_incoming,
      visibleConnectorWitnessAssemblyTopology_complex_point]
  obtain ⟨e0,Es,H,he0S,he0T,he0F,he0I,hH,_hImage,_hKEs,_hEsO,_hFEs,
      _hJEs,_hEsF,_hEsI,_hClosedEs,_hEsMatches⟩ :=
    visibleConnectorSourceInverse_global A.O_open A.F_smooth A.closed_round_in_domain
      A.F_jacobian_positive hpo hpi hnS hTraceFo hTraceFi
  have hFround : ContDiffOn ℝ ∞ A.F {q : Coord | 1 < planarRadius q ∧ planarRadius q < 2} :=
    A.F_smooth.mono (fun _ hq => A.closed_round_in_domain ⟨hq.1.le,hq.2.le⟩)
  obtain ⟨Ps,Hs,hNativeCont,hNativeRep,hHs,hPsS,hPsT,hPsActual,hPsSmooth,hPsInverse⟩ :=
    visibleConnectorSourceInverse_native_charts_of_actual_inverse L hnS hFround
      e0 he0S he0T he0F he0I H hH
  have hTraceGo : ∀ t,
      annularComplexConjugate (planarGradient A.G) (seamComplexCoord.symm (T.p (L*t))) =
        seamComplexCoord.symm (T.gamma (L*t)) := by
    intro t
    change seamComplexCoord.symm (planarGradient A.G
      (seamComplexCoord (seamComplexCoord.symm (T.p (L*t))))) = _
    rw [seamComplexCoord.apply_symm_apply,T.actual_gradient]
    rfl
  obtain ⟨hIncoming,hIncomingPair⟩ := visibleConnectorWitnessAssembly_incoming_germ D
    A.incoming_neighborhood_open A.incoming_curve_in_neighborhood A.incoming_germ_retained
  have hTraceGi : ∀ t,
      annularComplexConjugate (planarGradient A.G)
        (seamComplexCoord.symm (D.incoming.p (L*t))) =
        seamComplexCoord.symm (D.incoming.gamma (L*t)) := by
    intro t
    change seamComplexCoord.symm (planarGradient A.G
      (seamComplexCoord (seamComplexCoord.symm (D.incoming.p (L*t))))) = _
    rw [seamComplexCoord.apply_symm_apply,(hIncoming (L*t)).2]
  obtain ⟨Pg,Eg,Hg,_hPgRestr,hPgS,hPgT,hPgF,hPgSmooth,hPgInverse,hHg,_hGImage,
      hKEg,hEgU,_hGEg,hNEg,hEgF,hEgSmooth,hEgInverse,hClosedEg,hForward,hInverse,_hEgT⟩ :=
    visibleConnectorGradientInverseApplication_charts hpo hpi hgo hgi hnS hnG
      A.U_open A.G_smooth hKU hNeg hTraceGo hTraceGi
  let raw := visibleConnectorSourceInverseNativeRawSource L A.F
  let Vraw : Set Coord := {q | q 1 ∈ Ioo (0 : ℝ) 1}
  have hVraw : IsOpen Vraw := isOpen_Ioo.preimage (continuous_apply 1)
  have hRawSmooth : ContDiffOn ℝ ∞ raw Vraw :=
    visibleConnectorWitnessAssembly_native_raw_source_contDiffOn L A.F_smooth
      A.closed_round_in_domain
  have hRawMap : MapsTo raw Vraw (annularCoordJordanInterior Ho Hi) := by
    rw [← he0T]
    exact visibleConnectorWitnessAssembly_native_raw_source_mapsTo L e0 he0S he0F
  have hRawSign : ∀ q ∈ Vraw, (positiveExitJacobian raw q).det < 0 := by
    intro q hq
    have hRadius : planarRadius (saddlePolarChart ![1+q 1,2*Real.pi*q 0/L]) = 1+q 1 :=
      angularDescent_radius_polar (q := ![1+q 1,2*Real.pi*q 0/L]) (by
        change 0 < 1+q 1
        linarith [hq.1])
    have hK : saddlePolarChart ![1+q 1,2*Real.pi*q 0/L] ∈
        {z : Coord | 1 ≤ planarRadius z ∧ planarRadius z ≤ 2} := by
      change 1 ≤ planarRadius _ ∧ planarRadius _ ≤ 2
      rw [hRadius]
      constructor <;> linarith [hq.1,hq.2]
    exact visibleConnectorWitnessAssembly_native_raw_source_negative hL q
      (by linarith [hq.1])
      ((A.F_smooth.contDiffAt (A.O_open.mem_nhds (A.closed_round_in_domain hK))).differentiableAt (by simp))
      (A.F_jacobian_positive _ hK.1 hK.2)
  have hGradientSign : ∀ q ∈ Vraw,
      (positiveExitJacobian (planarGradient A.G ∘ raw) q).det > 0 := by
    intro q hq
    have hK : raw q ∈ annularCoordJordanClosure Ho Hi := by
      rw [← closure_annularCoordJordanInterior Ho Hi hnS]
      exact subset_closure (hRawMap hq)
    exact visibleConnectorWitnessAssembly_native_raw_gradient_positive A.U_open A.G_smooth
      q (hKU hK) ((hRawSmooth.contDiffAt (hVraw.mem_nhds hq)).differentiableAt (by simp))
      (hNeg _ hK) (hRawSign q hq)
  obtain ⟨hRawIncoming,hRawTerminal⟩ :=
    visibleConnectorWitnessAssembly_native_raw_source_endpoints L A.F D.incoming.p
      A.terminal.p A.source_incoming A.source_terminal
  have hTp : range T.p ⊆ Eg.source := by
    intro q hq
    apply hKEg
    rw [← hAnnS]
    exact frontier_subset_closure (hFrontS.symm ▸ Or.inr hq)
  have hTg : range T.gamma ⊆ Eg.target := by
    intro q hq
    apply hClosedEg
    rw [← hAnnG]
    exact frontier_subset_closure (hFrontG.symm ▸ Or.inl hq)
  have hCircle : {y : Coord | planarRadius y = R} ⊆ Eg.target :=
    visibleConnectorWitnessAssembly_terminal_circle_subset D.radius_pos
      A.theta_smooth.continuous A.theta_turn A.terminal_circle hTg
  refine ⟨{
    eta := A.eta
    eta_pos := A.eta_pos
    eta_small := A.eta_small
    G := A.G
    U := A.U
    U_open := A.U_open
    G_smooth := A.G_smooth
    source_annulus := annularCoordJordanInterior Ho Hi
    gradient_annulus := annularCoordJordanInterior To Ti
    source_annulus_open := annularCoordJordanInterior_isOpen Ho Hi
    gradient_annulus_open := annularCoordJordanInterior_isOpen To Ti
    source_closure_compact := by rwa [hAnnS] at hCompactS
    gradient_closure_compact := by rwa [hAnnG] at hCompactG
    source_closure_in_domain := by rwa [closure_annularCoordJordanInterior Ho Hi hnS]
    actual_saddle := fun q hq => hNeg q (by
      rw [← closure_annularCoordJordanInterior Ho Hi hnS]; exact subset_closure hq)
    terminal := T
    incoming_trace_retained := hIncoming
    incoming_neighborhood := A.incoming_neighborhood
    incoming_neighborhood_open := A.incoming_neighborhood_open
    incoming_curve_in_neighborhood := A.incoming_curve_in_neighborhood
    incoming_neighborhood_in_domains := A.incoming_neighborhood_in_domains
    incoming_germ_retained := A.incoming_germ_retained
    incoming_positive_pairing := hIncomingPair
    theta := A.theta
    theta_smooth := A.theta_smooth
    theta_increasing := A.theta_increasing
    theta_turn := A.theta_turn
    terminal_circle := A.terminal_circle
    terminal_radial_positive := A.terminal_radial_positive
    source_nesting := A.source_nesting
    gradient_nesting := A.gradient_nesting
    source_annulus_eq := hAnnS.symm
    gradient_annulus_eq := hAnnG.symm
    raw_source := raw
    raw_source_smooth := hRawSmooth
    raw_source_periodic := visibleConnectorWitnessAssembly_native_raw_source_periodic hL.ne' A.F
    raw_source_incoming := hRawIncoming
    raw_source_terminal := hRawTerminal
    raw_source_interior := hRawMap
    source_degree_sign := hRawSign
    gradient_degree_sign := hGradientSign
    native_source := visibleConnectorSourceInverseNativeSource L A.F
    native_source_continuous := hNativeCont
    native_source_actual := hNativeRep
    source_closure_chart := Hs
    source_closure_chart_actual := hHs
    source_chart := Ps
    source_chart_source := hPsS
    source_chart_target := hPsT
    source_chart_actual := hPsActual
    source_chart_smooth := hPsSmooth
    source_inverse_smooth := hPsInverse
    gradient_chart := Pg
    gradient_chart_source := hPgS
    gradient_chart_target := hPgT
    gradient_chart_actual := fun _ _ => congrFun hPgF _
    gradient_chart_smooth := hPgSmooth
    gradient_inverse_smooth := hPgInverse
    terminal_source_collar := Eg.source
    terminal_gradient_collar := Eg.target
    terminal_source_collar_open := Eg.open_source
    terminal_gradient_collar_open := Eg.open_target
    terminal_source_in_domain := hEgU
    terminal_source_in_collar := hTp
    terminal_gradient_in_collar := hTg
    terminal_circle_in_collar := hCircle
    terminal_saddle := hNEg
    terminal_gradient_chart := Eg
    terminal_gradient_chart_source := rfl
    terminal_gradient_chart_target := rfl
    terminal_gradient_chart_actual := fun _ _ => congrFun hEgF _
    terminal_gradient_chart_smooth := hEgSmooth
    terminal_gradient_inverse_smooth := hEgInverse
    terminal_chart_matches := hForward.mono inter_subset_right
    terminal_inverse_matches := hInverse.mono inter_subset_right
    gradient_closure_chart := Hg
    gradient_closure_chart_actual := hHg
    source_boundary_exact := by rwa [hAnnS] at hFrontS
    gradient_boundary_exact := by rw [← hAnnG,hFrontG,union_comm]
    source_boundaries_disjoint := hDisjointS
    gradient_boundaries_disjoint := hDisjointG.symm
    source_boundary_injective := by
      intro b
      cases b
      · exact D.incoming.source_injective
      · exact T.source_injective
    gradient_boundary_injective := by
      intro b
      cases b
      · exact D.incoming.gradient_injective
      · exact T.gradient_injective
  }⟩

/-- A family of ordinary final scalar/germ/boundary facts suffices for the
canonical connector construction statement. Existence of this family is the
remaining DESC obligation; it is not supplied by this assembly theorem. -/
theorem visibleConnectorWitnessAssembly_statement
    {Gin : Coord → ℝ} {Uin : Set Coord} {L R : ℝ} [Fact (0 < L)]
    (D : VisibleConnectorIncomingData Gin Uin L R)
    (hOrdinary : ∀ etaMax : ℝ, 0 < etaMax →
      Nonempty (VisibleConnectorWitnessAssemblyOrdinaryData D etaMax)) :
    VisibleConnectorConstructionStatement D := by
  intro etaMax hEta
  obtain ⟨A⟩ := hOrdinary etaMax hEta
  exact visibleConnectorWitnessAssembly_of_ordinary D A

end
end TightVer401
