import TightVer401.VisibleConnectorGradientInverseApplicationBoundary
import TightVer401.VisibleConnectorGradientInverseApplicationCollar

/-! Ordinary final potential and actual reverse-nested gradient boundaries
construct the whole gradient inverse and a SAME-map collar. Degree and compact
local inversion are reused; no gradient-chart conclusion is supplied. -/
namespace TightVer401
noncomputable section
open Set Function Filter OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false

/-- Actual negative Hessian and ordinary swapped positive Jordan traces
produce the interior chart, closed chart and one enlarged SAME gradient chart. -/
theorem visibleConnectorGradientInverseApplication_global
    {Ho Hi To Ti : ℂ ≃ₜ ℂ} {gammaOuter gammaInner etaOuter etaInner : ℝ → ℂ}
    (hSourceOuter : PositiveJordanParametrization Ho gammaOuter)
    (hSourceInner : PositiveJordanParametrization Hi gammaInner)
    (hTargetInner : PositiveJordanParametrization Ti etaOuter)
    (hTargetOuter : PositiveJordanParametrization To etaInner)
    (hSourceNested : closure (jordanInterior Hi) ⊆ jordanInterior Ho)
    (hTargetNested : closure (jordanInterior Ti) ⊆ jordanInterior To)
    {G : Coord → ℝ} {U : Set Coord} (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U)
    (hKU : annularCoordJordanClosure Ho Hi ⊆ U)
    (hNeg : ∀ z ∈ annularCoordJordanClosure Ho Hi, (planarHessian G z).det < 0)
    (hTraceOuter : ∀ t, annularComplexConjugate (planarGradient G) (gammaOuter t) = etaOuter t)
    (hTraceInner : ∀ t, annularComplexConjugate (planarGradient G) (gammaInner t) = etaInner t) :
    ∃ (e E : OpenPartialHomeomorph Coord Coord)
      (H : ↥(closure (annularCoordJordanInterior Ho Hi)) ≃ₜ
        ↥(closure (annularCoordJordanInterior To Ti))),
      e.source = annularCoordJordanInterior Ho Hi ∧
      e.target = annularCoordJordanInterior To Ti ∧
      (e : Coord → Coord) = planarGradient G ∧
      ContDiffOn ℝ ∞ e (annularCoordJordanInterior Ho Hi) ∧
      ContDiffOn ℝ ∞ e.symm (annularCoordJordanInterior To Ti) ∧
      (∀ z, (H z : Coord) = planarGradient G z) ∧
      planarGradient G '' closure (annularCoordJordanInterior Ho Hi) =
        closure (annularCoordJordanInterior To Ti) ∧
      closure (annularCoordJordanInterior Ho Hi) ⊆ E.source ∧ E.source ⊆ U ∧
      ContDiffOn ℝ ∞ G E.source ∧
      (∀ z ∈ E.source, (planarHessian G z).det < 0) ∧
      (E : Coord → Coord) = planarGradient G ∧
      ContDiffOn ℝ ∞ E E.source ∧ ContDiffOn ℝ ∞ E.symm E.target ∧
      closure (annularCoordJordanInterior To Ti) ⊆ E.target ∧
      EqOn E e (annularCoordJordanInterior Ho Hi) ∧
      EqOn E.symm e.symm (annularCoordJordanInterior To Ti) ∧
      E.target = planarGradient G '' E.source := by
  let Oc : Set ℂ := seamComplexCoord ⁻¹' U
  have hOc : IsOpen Oc := hU.preimage seamComplexCoord.continuous
  have hFc : ContDiffOn ℝ ∞ (annularComplexConjugate (planarGradient G)) Oc :=
    seamComplexCoord.symm.contDiff.comp_contDiffOn
      ((planarGradient_contDiffOn hG hU).comp seamComplexCoord.contDiff.contDiffOn
        (fun _ hz => hz))
  have hBoundary : frontier (jordanInterior Ho) ∪ frontier (jordanInterior Hi) ⊆ Oc := by
    intro z hz
    exact hKU (mem_image_of_mem seamComplexCoord
      (annular_jordan_boundary_subset_closure hSourceNested hz))
  obtain ⟨Bo,hBo,hWo⟩ := visibleConnectorGradientInverseApplication_ordinary_boundary
    hOc hFc hSourceOuter hTargetInner (fun _ hz => hBoundary (Or.inl hz)) hTraceOuter
  obtain ⟨Bi,hBi,hWi⟩ := visibleConnectorGradientInverseApplication_ordinary_boundary
    hOc hFc hSourceInner hTargetOuter (fun _ hz => hBoundary (Or.inr hz)) hTraceInner
  obtain ⟨e,heS,heT,heF,hei,H0,hH0⟩ :=
    annular_degree_planarGradient_global_diffeomorphism Ho Hi To Ti gammaOuter gammaInner
      hSourceOuter hSourceInner hSourceNested hTargetNested G U hU hG hKU (-1)
      (Or.inr rfl) (fun z hz => by
        have hzK : z ∈ annularCoordJordanClosure Ho Hi := by
          obtain ⟨w,hw,rfl⟩ := hz
          exact mem_image_of_mem seamComplexCoord (annularJordanInterior_subset_closure Ho Hi hw)
        simpa using neg_pos.mpr (hNeg z hzK)) true Bo Bi hBo hBi 1 (by norm_num) hWo hWi
  let H := ((Homeomorph.setCongr (closure_annularCoordJordanInterior Ho Hi hSourceNested)).trans H0).trans
    (Homeomorph.setCongr (closure_annularCoordJordanInterior To Ti hTargetNested).symm)
  have hH : ∀ z, (H z : Coord) = planarGradient G z := fun z => hH0 _
  have hImage : planarGradient G '' closure (annularCoordJordanInterior Ho Hi) =
      closure (annularCoordJordanInterior To Ti) := by
    apply Subset.antisymm
    · rintro y ⟨z,hz,rfl⟩
      rw [← hH ⟨z,hz⟩]
      exact (H ⟨z,hz⟩).property
    · intro y hy
      obtain ⟨z,hzy⟩ := H.surjective ⟨y,hy⟩
      exact ⟨z,z.property,(hH z).symm.trans (congrArg Subtype.val hzy)⟩
  have hInj : InjOn (planarGradient G) (closure (annularCoordJordanInterior Ho Hi)) := by
    intro z hz w hw he
    exact congrArg Subtype.val (H.injective (Subtype.ext
      ((hH ⟨z,hz⟩).trans (he.trans (hH ⟨w,hw⟩).symm))))
  have hClosed : IsCompact (closure (annularCoordJordanInterior Ho Hi)) := by
    rw [closure_annularCoordJordanInterior Ho Hi hSourceNested]
    exact annularCoordJordanClosure_isCompact Ho Hi
  have hClosedU : closure (annularCoordJordanInterior Ho Hi) ⊆ U := by
    rw [closure_annularCoordJordanInterior Ho Hi hSourceNested]
    exact hKU
  have hClosedNeg : ∀ z ∈ closure (annularCoordJordanInterior Ho Hi),
      (planarHessian G z).det < 0 := by
    rw [closure_annularCoordJordanInterior Ho Hi hSourceNested]
    exact hNeg
  obtain ⟨E,hKE,hEU,hGE,hNE,hEF,hES,hEI,hImageE,hET⟩ :=
    visibleConnectorGradientInverseApplication_exists_collar hU hG hClosed hClosedU hClosedNeg hInj
  have heK : e.source ⊆ closure (annularCoordJordanInterior Ho Hi) := by
    rw [heS]
    exact subset_closure
  have heActual : EqOn e (planarGradient G) e.source := fun z _ => congrFun heF z
  obtain ⟨_heTarget,hForward,hInverse⟩ :=
    visibleConnectorGradientInverseApplication_collar_agrees hKE hEF heK heActual
  have hInteriorU : annularCoordJordanInterior Ho Hi ⊆ U := subset_closure.trans hClosedU
  refine ⟨e,E,H,heS,heT,heF,?_,?_,hH,hImage,hKE,hEU,hGE,hNE,hEF,hES,hEI,
    ?_,?_,?_,hET⟩
  · rw [heF]
    exact (planarGradient_contDiffOn hG hU).mono hInteriorU
  · simpa only [heT] using hei
  · rw [← hImage]
    exact hImageE
  · simpa only [heS] using hForward
  · simpa only [heT] using hInverse

end
end TightVer401