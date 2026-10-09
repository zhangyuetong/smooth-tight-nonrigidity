import TightVer401.VisibleConnectorGradientInverseApplicationRestriction
import TightVer401.QuadraticRadialFillingCircle

/-! Final actual potential adapter. Ordinary retained boundary equations and
negative actual Hessian are explicit inputs. The raw and final glued potentials
are never silently identified; either supplied literal potential uses this API. -/
namespace TightVer401
noncomputable section
open Set Function Filter Metric OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false

/-- Actual negative Hessian and ordinary swapped positive Jordan traces
produce the interior chart, closed chart and one enlarged SAME gradient chart. -/
theorem visibleConnectorGradientInverseApplication_charts
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
    ∃ (P E : OpenPartialHomeomorph Coord Coord)
      (H : ↥(closure (annularCoordJordanInterior Ho Hi)) ≃ₜ
        ↥(closure (annularCoordJordanInterior To Ti))),
      P = visibleConnectorGradientInverseApplication_restricted_chart E
        (annularCoordJordanInterior Ho Hi) (annularCoordJordanInterior_isOpen Ho Hi) ∧
      P.source = annularCoordJordanInterior Ho Hi ∧
      P.target = annularCoordJordanInterior To Ti ∧
      (P : Coord → Coord) = planarGradient G ∧
      ContDiffOn ℝ ∞ P (annularCoordJordanInterior Ho Hi) ∧
      ContDiffOn ℝ ∞ P.symm (annularCoordJordanInterior To Ti) ∧
      (∀ z, (H z : Coord) = planarGradient G z) ∧
      planarGradient G '' closure (annularCoordJordanInterior Ho Hi) =
        closure (annularCoordJordanInterior To Ti) ∧
      closure (annularCoordJordanInterior Ho Hi) ⊆ E.source ∧ E.source ⊆ U ∧
      ContDiffOn ℝ ∞ G E.source ∧
      (∀ z ∈ E.source, (planarHessian G z).det < 0) ∧
      (E : Coord → Coord) = planarGradient G ∧
      ContDiffOn ℝ ∞ E E.source ∧ ContDiffOn ℝ ∞ E.symm E.target ∧
      closure (annularCoordJordanInterior To Ti) ⊆ E.target ∧
      EqOn E P (annularCoordJordanInterior Ho Hi) ∧
      EqOn E.symm P.symm (annularCoordJordanInterior To Ti) ∧
      E.target = planarGradient G '' E.source := by
  obtain ⟨e,E,H,heS,heT,heF,heSmooth,hei,hH,hImage,hKE,hEU,hGE,hNE,hEF,hES,hEI,
    hClosedTarget,_hForward,_hInverse,hET⟩ :=
    visibleConnectorGradientInverseApplication_global hSourceOuter hSourceInner hTargetInner
      hTargetOuter hSourceNested hTargetNested hU hG hKU hNeg hTraceOuter hTraceInner
  have hVE : annularCoordJordanInterior Ho Hi ⊆ E.source := subset_closure.trans hKE
  have hSourceImage : planarGradient G '' annularCoordJordanInterior Ho Hi =
      annularCoordJordanInterior To Ti := by
    rw [← heF,← heS, e.image_source_eq_target,heT]
  let P := visibleConnectorGradientInverseApplication_restricted_chart E
    (annularCoordJordanInterior Ho Hi) (annularCoordJordanInterior_isOpen Ho Hi)
  obtain ⟨hPS,hPT,hPF,hPSmooth,hPInverse,hForward,hInverse⟩ :=
    visibleConnectorGradientInverseApplication_restricted_chart_properties
      (annularCoordJordanInterior_isOpen Ho Hi) hVE hEF hSourceImage hES hEI
  exact ⟨P,E,H,rfl,hPS,hPT,hPF,hPSmooth,hPInverse,hH,hImage,hKE,hEU,hGE,hNE,hEF,
    hES,hEI,hClosedTarget,hForward,hInverse,hET⟩

/-- Both literal ordinary terminal traces lie in the whole closed-band collars. -/
theorem visibleConnectorGradientInverseApplication_terminal_traces_in_collars
    {Ho Hi To Ti : ℂ ≃ₜ ℂ} {gamma eta : ℝ → ℂ} {E : OpenPartialHomeomorph Coord Coord}
    (hSource : PositiveJordanParametrization Ho gamma)
    (hTarget : PositiveJordanParametrization Ti eta)
    (hnS : closure (jordanInterior Hi) ⊆ jordanInterior Ho)
    (hnT : closure (jordanInterior Ti) ⊆ jordanInterior To)
    (hSourceE : closure (annularCoordJordanInterior Ho Hi) ⊆ E.source)
    (hTargetE : closure (annularCoordJordanInterior To Ti) ⊆ E.target) :
    range (fun t => seamComplexCoord (gamma t)) ⊆ E.source ∧
      range (fun t => seamComplexCoord (eta t)) ⊆ E.target := by
  constructor
  · rintro y ⟨t,rfl⟩
    apply hSourceE
    rw [closure_annularCoordJordanInterior Ho Hi hnS]
    exact mem_image_of_mem seamComplexCoord
      (annular_jordan_boundary_subset_closure hnS (Or.inl (hSource.toRegular.mem_frontier t)))
  · rintro y ⟨t,rfl⟩
    apply hTargetE
    rw [closure_annularCoordJordanInterior To Ti hnT]
    exact mem_image_of_mem seamComplexCoord
      (annular_jordan_boundary_subset_closure hnT (Or.inr (hTarget.toRegular.mem_frontier t)))

/-- A round actual inner gradient boundary includes the entire terminal circle
in the enlarged gradient target, including every phase. -/
theorem visibleConnectorGradientInverseApplication_terminal_circle_in_target
    {R : ℝ} (hR : 0 < R) {To : ℂ ≃ₜ ℂ} {T : Set Coord}
    (hNested : closure (jordanInterior (roundDiskChart R hR)) ⊆ jordanInterior To)
    (hClosedT : closure (annularCoordJordanInterior To (roundDiskChart R hR)) ⊆ T) :
    {y : Coord | planarRadius y = R} ⊆ T := by
  intro y hy
  have hz : seamComplexCoord.symm y ∈ frontier (jordanInterior (roundDiskChart R hR)) := by
    rw [roundDiskChart_interior,frontier_ball _ hR.ne',mem_sphere_zero_iff_norm]
    rw [← quadraticRadialFillingRadius_complex,seamComplexCoord.apply_symm_apply]
    exact hy
  apply hClosedT
  rw [closure_annularCoordJordanInterior To (roundDiskChart R hR) hNested]
  exact ⟨seamComplexCoord.symm y,
    annular_jordan_boundary_subset_closure hNested (Or.inr hz),seamComplexCoord.apply_symm_apply y⟩

end
end TightVer401
