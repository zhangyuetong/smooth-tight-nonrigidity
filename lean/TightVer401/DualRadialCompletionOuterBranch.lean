import TightVer401.DualRadialCompletionOuterPatch
import TightVer401.DualRadialCompletionRetainedContour
import TightVer401.DualRadialCompletionNeckRecovery

/-! Assemble the actual outgoing branch from the same connector and actual
neck Legendre tail, through the actual retained contour. The original supplied
Jordan filling determines the incoming region. -/
namespace TightVer401
noncomputable section
open Set Filter Metric OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

/-- Actual contour nesting derives the patch carrier, incoming neighborhood
and all overlap premises for the same outgoing connector and neck dual. -/
theorem exists_dualRadialCompletion_outer_branch
    {Gin : Coord → ℝ} {Uin : Set Coord} {L R etaMax : ℝ} [Fact (0 < L)]
    {D : VisibleConnectorIncomingData Gin Uin L R}
    (C : VisibleConnectorConstructionData D etaMax)
    (eC eN : OpenPartialHomeomorph Coord Coord)
    (hClosed : closure C.source_annulus ⊆ eC.source)
    (hC : ContDiffOn ℝ ∞ C.G eC.source)
    (hnC : ∀ p ∈ eC.source, (planarHessian C.G p).det < 0)
    {Fneck : Coord → ℝ} {HOld Gamma0 GammaS : ℂ ≃ₜ ℂ}
    (hOldRange : range (positiveExitComplexTrace D.incoming.p) = HOld '' sphere (0 : ℂ) 1)
    (hOldNested : closure (positiveExitInside D.incoming.p) ⊆ seamComplexCoord '' jordanInterior Gamma0)
    (hGammaNested : seamComplexCoord '' closure (jordanInterior GammaS) ⊆
      seamComplexCoord '' jordanInterior Gamma0)
    (hTerminalNested : seamComplexCoord '' closure (jordanInterior Gamma0) ⊆
      positiveExitInside C.terminal.p)
    (hNeckTarget : eN.target = seamComplexCoord '' (univ \ GammaS '' closedBall (0 : ℂ) 1))
    (hTail : ContDiffOn ℝ ∞ (planarLegendre Fneck eN) eN.target)
    (hnTail : ∀ p ∈ eN.target, (planarHessian (planarLegendre Fneck eN) p).det < 0)
    {V : Set Coord} (hV : IsOpen V)
    (hFrontierV : seamComplexCoord '' (Gamma0 '' sphere (0 : ℂ) 1) ⊆ V)
    (hVC : V ⊆ eC.source) (hVT : V ⊆ eN.target)
    (hRecovery : EqOn (planarLegendre Fneck eN) C.G V)
    {A B Cneck T0 : ℝ}
    (hLiteral : EqOn (planarLegendre Fneck eN)
      (fun p => A*planarRadius p-B/planarRadius p-Cneck) {p | T0 < planarRadius p}) :
    ∃ (Fo : Coord → ℝ) (Uo Nout : Set Coord) (Lout : ℝ),
      IsOpen Uo ∧ IsOpen Nout ∧ Nout ⊆ Uin ∧
      frontier (seamComplexCoord '' (HOld '' ball (0 : ℂ) 1)) ⊆ Nout ∧
      (((closure (seamComplexCoord '' (HOld '' ball (0 : ℂ) 1)))ᶜ ∩
        {p : Coord | 0 < planarRadius p}) ∪ Nout) ⊆ Uo ∧
      ContDiffOn ℝ ∞ Fo Uo ∧ (∀ p ∈ Uo, (planarHessian Fo p).det < 0) ∧
      EqOn Fo Gin Nout ∧ (∀ p ∈ Nout, Fo =ᶠ[𝓝 p] Gin) ∧
      0 < Lout ∧
      EqOn Fo (fun p => A*planarRadius p-B/planarRadius p-Cneck)
        {p | Lout < planarRadius p} ∧
      (∀ p, Lout < planarRadius p →
        Fo =ᶠ[𝓝 p] (fun q => A*planarRadius q-B/planarRadius q-Cneck)) := by
  let I := positiveExitInside D.incoming.p
  let J := seamComplexCoord '' jordanInterior Gamma0
  let N := C.incoming_neighborhood ∩ eC.source
  have hI : I = seamComplexCoord '' (HOld '' ball (0 : ℂ) 1) :=
    dualRadialCompletionTraceInside_eq_of_range hOldRange D.incoming.source_jordan
  have hJ : IsOpen J := seamComplexCoord.isOpenMap _ (jordanInterior_isOpen Gamma0)
  have hJCompact : IsCompact (closure J) := by
    rw [show closure J = seamComplexCoord '' closure (jordanInterior Gamma0) from
      (seamComplexCoord.image_closure _).symm]
    exact (isCompact_closure_jordanInterior Gamma0).image seamComplexCoord.continuous
  have h0J : (0 : Coord) ∈ J := hOldNested (subset_closure D.incoming.source_enclosure)
  have hConnector : J \ closure I ⊆ eC.source := by
    intro p hp
    have hpAnnulus : p ∈ C.source_annulus := by
      rw [C.source_annulus_eq]
      exact ⟨hTerminalNested (by
        rw [seamComplexCoord.image_closure]
        exact subset_closure hp.1),hp.2⟩
    exact hClosed (subset_closure hpAnnulus)
  have hExterior : (closure J)ᶜ ∩ {p : Coord | 0 < planarRadius p} ⊆ eN.target := by
    intro p hp
    rw [hNeckTarget]
    refine ⟨seamComplexCoord.symm p, ⟨mem_univ _,?_⟩,seamComplexCoord.apply_symm_apply p⟩
    intro hz
    apply hp.1
    apply subset_closure
    apply hGammaNested
    refine ⟨seamComplexCoord.symm p,?_,seamComplexCoord.apply_symm_apply p⟩
    rwa [closure_jordanInterior]
  have hFrontierJ : frontier J ⊆ V := by
    rw [show frontier J = seamComplexCoord '' (Gamma0 '' sphere (0 : ℂ) 1) from by
      change frontier ((seamComplexCoord.toHomeomorph : ℂ → Coord) '' jordanInterior Gamma0) =
        seamComplexCoord '' (Gamma0 '' sphere (0 : ℂ) 1)
      rw [← seamComplexCoord.toHomeomorph.image_frontier,frontier_jordanInterior]
      try rfl]
    exact hFrontierV
  have hN : IsOpen N := C.incoming_neighborhood_open.inter eC.open_source
  have hNC : N ⊆ eC.source := inter_subset_right
  have hNSource : N ⊆ Uin := fun p hp => (C.incoming_neighborhood_in_domains hp.1).2
  have hFrontierI : frontier I = range D.incoming.p := by
    calc
      frontier I = seamComplexCoord '' (HOld '' sphere (0 : ℂ) 1) := by
        rw [hI]
        change frontier ((seamComplexCoord.toHomeomorph : ℂ → Coord) ''
          (HOld '' ball (0 : ℂ) 1)) = seamComplexCoord '' (HOld '' sphere (0 : ℂ) 1)
        rw [← seamComplexCoord.toHomeomorph.image_frontier,← HOld.image_frontier,
          frontier_ball _ one_ne_zero]
        try rfl
      _ = seamComplexCoord '' range (positiveExitComplexTrace D.incoming.p) := by rw [hOldRange]
      _ = range (seamComplexCoord ∘ positiveExitComplexTrace D.incoming.p) := (range_comp (seamComplexCoord : ℂ → Coord) (positiveExitComplexTrace D.incoming.p)).symm
      _ = range D.incoming.p := by
        congr 1
        funext s
        ext i
        fin_cases i <;> rfl
  have hIncoming : frontier I ⊆ N := by
    rw [hFrontierI]
    rintro p ⟨s,rfl⟩
    refine ⟨C.incoming_curve_in_neighborhood (mem_range_self s),hClosed ?_⟩
    apply frontier_subset_closure
    rw [C.source_boundary_exact]
    exact Or.inl (mem_range_self s)
  have hIncomingPositive : frontier I ⊆ {p : Coord | 0 < planarRadius p} := by
    rw [hFrontierI]
    rintro p ⟨s,rfl⟩
    change 0 < planarRadius (D.incoming.p s)
    rw [← angularDescentComplex_norm]
    apply norm_pos_iff.mpr
    intro hz
    apply D.incoming.source_nonzero s
    simpa only [quadraticRadialFillingCoord_complex,map_zero] using congrArg seamComplexCoord hz
  have hRetained : EqOn C.G Gin N := fun p hp => C.incoming_germ_retained hp.1
  obtain ⟨Fo,Uo,Nout,Lout,hUo,hNout,hNoutN,hFront,hCover,hFo,hnFo,hEq,hL,hEnd⟩ :=
    exists_dualRadialCompletion_outer_patch hJ hJCompact h0J hOldNested
      eC.open_source eN.open_target hN hV hConnector hExterior hFrontierJ hVC hVT
      hNC hIncoming hIncomingPositive hC hTail hnC hnTail
      (fun p hp => (hRecovery hp).symm) hRetained hLiteral
  refine ⟨Fo,Uo,Nout,Lout,hUo,hNout,(fun p hp => hNSource (hNoutN hp)),?_,?_,
    hFo,hnFo,hEq,?_,hL,hEnd,?_⟩
  · rwa [← hI]
  · rwa [← hI]
  · intro p hp
    filter_upwards [hNout.mem_nhds hp] with q hq
    exact hEq hq
  · intro p hp
    have hOpen : IsOpen {q : Coord | Lout < planarRadius q} :=
      isOpen_lt continuous_const quadraticFillerCartesianGradient_radius_continuous
    filter_upwards [hOpen.mem_nhds hp] with q hq
    exact hEnd hq

end
end TightVer401
