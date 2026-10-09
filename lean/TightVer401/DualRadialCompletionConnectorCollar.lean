import TightVer401.VisibleConnectorContract
import TightVer401.DualRadialCompletionGlobalInverse
import TightVer401.QuadraticRadialFillingBoundaryGerms

/-! The actual connector's compact closure admits one actual smooth gradient
inverse collar. This is derived from its boundary homeomorphism and Hessian
signs; it is not an additional connector output premise. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix

theorem exists_dualRadialCompletion_connector_collar
    {Gin : Coord → ℝ} {Uin : Set Coord} {L R etaMax : ℝ} [Fact (0 < L)]
    {D : VisibleConnectorIncomingData Gin Uin L R}
    (C : VisibleConnectorConstructionData D etaMax) :
    ∃ e : OpenPartialHomeomorph Coord Coord,
      closure C.source_annulus ⊆ e.source ∧ e.source ⊆ C.U ∧
      ContDiffOn ℝ ∞ C.G e.source ∧
      (∀ p ∈ e.source, (planarHessian C.G p).det < 0) ∧
      (e : Coord → Coord) = planarGradient C.G ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧
      C.gradient_annulus ⊆ e.target ∧
      EqOn e.symm C.gradient_chart.symm C.gradient_annulus := by
  have hNeg : ∀ p ∈ closure C.source_annulus, (planarHessian C.G p).det < 0 := by
    intro p hp
    by_cases hpa : p ∈ C.source_annulus
    · exact C.actual_saddle p hpa
    have hFront : p ∈ frontier C.source_annulus := by
      rw [frontier, C.source_annulus_open.interior_eq]
      exact ⟨hp, hpa⟩
    rw [C.source_boundary_exact] at hFront
    rcases hFront with ⟨s, rfl⟩ | ⟨s, rfl⟩
    · have hNear := C.incoming_curve_in_neighborhood (mem_range_self s)
      have hGerm : C.G =ᶠ[𝓝 (D.incoming.p s)] Gin := by
        filter_upwards [C.incoming_neighborhood_open.mem_nhds hNear] with q hq
        exact C.incoming_germ_retained hq
      rw [quadraticRadialFilling_hessian_eq_of_germ hGerm]
      exact D.potential_saddle _ (C.incoming_neighborhood_in_domains hNear).2
    · exact C.terminal_saddle _ (C.terminal_source_in_collar (mem_range_self s))
  let V := C.U ∩ (fun p => (planarHessian C.G p).det) ⁻¹' Iio (0 : ℝ)
  have hV : IsOpen V :=
    (planarHessian_det_contDiffOn C.G_smooth C.U_open).continuousOn.isOpen_inter_preimage
      C.U_open isOpen_Iio
  have hClosedV : closure C.source_annulus ⊆ V :=
    fun p hp => ⟨C.source_closure_in_domain hp, hNeg p hp⟩
  have hInj : InjOn (planarGradient C.G) (closure C.source_annulus) := by
    intro p hp q hq heq
    have he : C.gradient_closure_chart ⟨p, hp⟩ = C.gradient_closure_chart ⟨q, hq⟩ := by
      apply Subtype.ext
      simpa only [C.gradient_closure_chart_actual] using heq
    exact congrArg Subtype.val (C.gradient_closure_chart.injective he)
  have hCont : ∀ p ∈ closure C.source_annulus, ContinuousAt (planarGradient C.G) p := by
    intro p hp
    exact (planarGradient_contDiffOn C.G_smooth C.U_open).contDiffAt
      (C.U_open.mem_nhds (C.source_closure_in_domain hp)) |>.continuousAt
  have hLocal : ∀ p ∈ closure C.source_annulus,
      ∃ W ∈ 𝓝 p, InjOn (planarGradient C.G) W := by
    intro p hp
    obtain ⟨e, he, _heU, hef, _hei⟩ := planarGradient_exists_smooth_local_inverse_at
      C.G_smooth C.U_open (C.source_closure_in_domain hp) (hNeg p hp).ne
    refine ⟨e.source, e.open_source.mem_nhds he, ?_⟩
    rw [← hef]
    exact e.injOn
  obtain ⟨W, hW, hCW, hIW⟩ := hInj.exists_isOpen_superset
    C.source_closure_compact hCont hLocal
  let Z := W ∩ V
  have hZ : IsOpen Z := hW.inter hV
  have hCZ : closure C.source_annulus ⊆ Z := fun p hp => ⟨hCW hp, hClosedV hp⟩
  have hZU : Z ⊆ C.U := fun _ hp => hp.2.1
  have hGZ := C.G_smooth.mono hZU
  have hNZ : ∀ p ∈ Z, (planarHessian C.G p).det < 0 := fun _ hp => hp.2.2
  have hIZ : InjOn (planarGradient C.G) Z := hIW.mono inter_subset_left
  have hJ : ∀ p ∈ Z, annularJacobian (planarGradient C.G) p ≠ 0 := by
    intro p hp
    rw [dualRadialCompletion_gradient_jacobian hGZ hZ hp]
    exact (hNZ p hp).ne
  have hUnique : ∀ y ∈ planarGradient C.G '' Z,
      ∃! p, p ∈ Z ∧ planarGradient C.G p = y := by
    rintro y ⟨p, hp, hpy⟩
    refine ⟨p, ⟨hp, hpy⟩, ?_⟩
    intro q hq
    exact hIZ hq.1 hp (hq.2.trans hpy.symm)
  obtain ⟨e, hes, _het, hef, hei⟩ := annular_exists_smooth_image_inverse hZ
    (planarGradient_contDiffOn hGZ hZ) hJ hUnique
  have hCE : closure C.source_annulus ⊆ e.source := by simpa only [hes] using hCZ
  have hOldSource : ∀ y ∈ C.gradient_annulus, C.gradient_chart.symm y ∈ C.source_annulus := by
    intro y hy
    rw [← C.gradient_chart_source]
    exact C.gradient_chart.map_target (by simpa only [C.gradient_chart_target] using hy)
  have hForward : ∀ y ∈ C.gradient_annulus,
      e (C.gradient_chart.symm y) = y := by
    intro y hy
    rw [hef, ← C.gradient_chart_actual (hOldSource y hy)]
    exact C.gradient_chart.right_inv (by simpa only [C.gradient_chart_target] using hy)
  refine ⟨e, hCE, ?_, ?_, ?_, hef, hei, ?_, ?_⟩
  · simpa only [hes] using hZU
  · simpa only [hes] using hGZ
  · simpa only [hes] using hNZ
  · intro y hy
    rw [← hForward y hy]
    exact e.map_source (hCE (subset_closure (hOldSource y hy)))
  · intro y hy
    calc
      e.symm y = e.symm (e (C.gradient_chart.symm y)) :=
        congrArg e.symm (hForward y hy).symm
      _ = C.gradient_chart.symm y := e.left_inv (hCE (subset_closure (hOldSource y hy)))

end
end TightVer401
