import TightVer401.DualRadialCompletionIncoming
import TightVer401.VisibleConnectorContract
import TightVer401.QuadraticRadialFillingBoundaryGerms

/-! Actual open scalar retention after the inner connector's reflected dual
is transformed back through its constructed gradient collar. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix ComplexConjugate

/-- Literal scalar recovery through the same reflected dual and reflected
inverse. Only the original actual partial inverse identity is needed. -/
theorem dualRadialCompletionInnerRetain_dual_recovery
    (G : Coord → ℝ) (e0 : OpenPartialHomeomorph Coord Coord)
    {y : Coord} (hy : dualRadialCompletionReflection y ∈ e0.source) :
    planarLegendre (dualRadialCompletionIncomingDual G e0)
      (dualRadialCompletionIncomingChart e0) y = G (dualRadialCompletionReflection y) := by
  change (dualRadialCompletionIncomingChart e0).symm y ⬝ᵥ y -
    (e0.symm (dualRadialCompletionReflection ((dualRadialCompletionIncomingChart e0).symm y)) ⬝ᵥ
      dualRadialCompletionReflection ((dualRadialCompletionIncomingChart e0).symm y) -
      G (e0.symm (dualRadialCompletionReflection ((dualRadialCompletionIncomingChart e0).symm y)))) = _
  rw [dualRadialCompletionIncomingChart_symm_apply,
    dualRadialCompletionReflection_involutive, e0.left_inv hy]
  have hDot : dualRadialCompletionReflection (e0 (dualRadialCompletionReflection y)) ⬝ᵥ y =
      dualRadialCompletionReflection y ⬝ᵥ e0 (dualRadialCompletionReflection y) := by
    calc
      _ = dualRadialCompletionReflection (e0 (dualRadialCompletionReflection y)) ⬝ᵥ
          dualRadialCompletionReflection (dualRadialCompletionReflection y) := by
        rw [dualRadialCompletionReflection_involutive]
      _ = e0 (dualRadialCompletionReflection y) ⬝ᵥ dualRadialCompletionReflection y :=
        dualRadialCompletionReflection_dot _ _
      _ = _ := dotProduct_comm _ _
  rw [hDot]
  ring

/-- The actual incoming scalar germ and constructed connector collar give an
open retained neighborhood of the original physical inner seam. -/
theorem exists_dualRadialCompletionInnerRetain
    {G : Coord → ℝ} (e0 : OpenPartialHomeomorph Coord Coord)
    (hG : ContDiffOn ℝ ∞ G e0.source)
    (hNegative : ∀ q ∈ e0.source, (planarHessian G q).det < 0)
    (heG : ∀ q ∈ e0.source, e0 q = planarGradient G q)
    (hInverse : ContDiffOn ℝ ∞ e0.symm e0.target)
    {L R etaMax : ℝ} [Fact (0 < L)]
    {D : VisibleConnectorIncomingData (dualRadialCompletionIncomingDual G e0)
      (dualRadialCompletionIncomingChart e0).source L R}
    (C : VisibleConnectorConstructionData D etaMax)
    (eC : OpenPartialHomeomorph Coord Coord)
    (hClosed : closure C.source_annulus ⊆ eC.source)
    (hActualC : (eC : Coord → Coord) = planarGradient C.G)
    {pMinus : ℝ → ℂ}
    (hDgamma : D.incoming.gamma = seamComplexCoord ∘ corrugatedReverseReflect pMinus) :
    ∃ W : Set Coord, IsOpen W ∧ range (seamComplexCoord ∘ pMinus) ⊆ W ∧
      W ⊆ e0.source ∧ W ⊆ dualRadialCompletionReflection ⁻¹' eC.target ∧
      EqOn (fun p => planarLegendre C.G eC (dualRadialCompletionReflection p)) G W ∧
      ∀ p ∈ W, (fun q => planarLegendre C.G eC (dualRadialCompletionReflection q)) =ᶠ[𝓝 p] G := by
  let eJ := dualRadialCompletionIncomingChart e0
  let Gin := dualRadialCompletionIncomingDual G e0
  obtain ⟨_hGin, _hGinNegative, hJActual, _hJInverse⟩ :=
    dualRadialCompletionIncoming_dual_data e0 hG hNegative heG hInverse
  let V : Set Coord := eJ.target ∩ eJ.symm ⁻¹' (C.incoming_neighborhood ∩ eC.source)
  have hVopen : IsOpen V := eJ.symm.continuousOn.isOpen_inter_preimage eJ.open_target
    (C.incoming_neighborhood_open.inter eC.open_source)
  have hOverlap : ∀ y ∈ V, y ∈ eC.target ∧
      planarLegendre C.G eC y = planarLegendre Gin eJ y := by
    intro y hy
    let q := eJ.symm y
    have hqJ : q ∈ eJ.source := eJ.map_target hy.1
    have hqN : q ∈ C.incoming_neighborhood := hy.2.1
    have hqC : q ∈ eC.source := hy.2.2
    have hGerm : C.G =ᶠ[𝓝 q] Gin := by
      filter_upwards [C.incoming_neighborhood_open.mem_nhds hqN] with z hz
      exact C.incoming_germ_retained hz
    have hGrad := quadraticRadialFilling_gradient_eq_of_germ hGerm
    have hForward : eC q = y := by
      calc
        eC q = planarGradient C.G q := congrFun hActualC q
        _ = planarGradient Gin q := hGrad
        _ = eJ q := (hJActual hqJ).symm
        _ = y := eJ.right_inv hy.1
    have hyC : y ∈ eC.target := by
      rw [← hForward]
      exact eC.map_source hqC
    have hInv : eC.symm y = q := by
      calc
        eC.symm y = eC.symm (eC q) := congrArg eC.symm hForward.symm
        _ = q := eC.left_inv hqC
    refine ⟨hyC, ?_⟩
    change eC.symm y ⬝ᵥ y - C.G (eC.symm y) = q ⬝ᵥ y - Gin q
    rw [hInv, C.incoming_germ_retained hqN]
  have hTraceSource (s : ℝ) : D.incoming.p s ∈ eJ.source :=
    D.incoming.p_in_domain (mem_univ s)
  have hTraceForward (s : ℝ) : eJ (D.incoming.p s) = D.incoming.gamma s :=
    (hJActual (hTraceSource s)).trans (congrFun D.incoming.actual_gradient s).symm
  have hTraceClosure (s : ℝ) : D.incoming.p s ∈ closure C.source_annulus := by
    apply frontier_subset_closure
    rw [C.source_boundary_exact]
    exact Or.inl (mem_range_self s)
  have hTraceV (s : ℝ) : D.incoming.gamma s ∈ V := by
    have hTarget : D.incoming.gamma s ∈ eJ.target := by
      rw [← hTraceForward s]
      exact eJ.map_source (hTraceSource s)
    have hInv : eJ.symm (D.incoming.gamma s) = D.incoming.p s := by
      rw [← hTraceForward s]
      exact eJ.left_inv (hTraceSource s)
    refine ⟨hTarget, ?_⟩
    change eJ.symm (D.incoming.gamma s) ∈ C.incoming_neighborhood ∩ eC.source
    rw [hInv]
    exact ⟨C.incoming_curve_in_neighborhood (mem_range_self s), hClosed (hTraceClosure s)⟩
  let W : Set Coord := dualRadialCompletionReflection ⁻¹' V
  have hWopen : IsOpen W := hVopen.preimage dualRadialCompletionReflection.continuous
  have hWsource : W ⊆ e0.source := by
    intro p hp
    have hTarget : dualRadialCompletionReflection p ∈ eJ.target := hp.1
    change dualRadialCompletionReflection p ∈ (dualRadialCompletionIncomingChart e0).target at hTarget
    rw [dualRadialCompletionIncomingChart_target] at hTarget
    change dualRadialCompletionReflection (dualRadialCompletionReflection p) ∈ e0.source at hTarget
    simpa only [dualRadialCompletionReflection_involutive] using hTarget
  have hWtarget : W ⊆ dualRadialCompletionReflection ⁻¹' eC.target :=
    fun p hp => (hOverlap (dualRadialCompletionReflection p) hp).1
  have hEq : EqOn (fun p => planarLegendre C.G eC (dualRadialCompletionReflection p)) G W := by
    intro p hp
    calc
      _ = planarLegendre Gin eJ (dualRadialCompletionReflection p) :=
        (hOverlap _ hp).2
      _ = G (dualRadialCompletionReflection (dualRadialCompletionReflection p)) :=
        dualRadialCompletionInnerRetain_dual_recovery G e0
          (by simpa only [dualRadialCompletionReflection_involutive] using hWsource hp)
      _ = G p := by rw [dualRadialCompletionReflection_involutive]
  refine ⟨W, hWopen, ?_, hWsource, hWtarget, hEq, ?_⟩
  · rintro p ⟨s, rfl⟩
    change dualRadialCompletionReflection (seamComplexCoord (pMinus s)) ∈ V
    have he : dualRadialCompletionReflection (seamComplexCoord (pMinus s)) = D.incoming.gamma (-s) := by
      rw [hDgamma]
      change dualRadialCompletionReflection (seamComplexCoord (pMinus s)) =
        seamComplexCoord (conj (pMinus (-(-s))))
      rw [neg_neg, dualRadialCompletionIncoming_complex_reflection]
    rw [he]
    exact hTraceV (-s)
  · intro p hp
    filter_upwards [hWopen.mem_nhds hp] with q hq
    exact hEq hq

end
end TightVer401
