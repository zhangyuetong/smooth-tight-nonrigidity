import TightVer401.CompletedSaddleAnnulusGraphCurvature
import TightVer401.PolarSaddleSignLocal
import TightVer401.SeamCoordinateInverse
import TightVer401.CurvatureLocality
import OAI.Geometry.WeakMTW.Analysis.IntegralEquation

/-! Actual curvature transfer through curved smooth charts for the same
completed graphs. The normal and second form are constructed from actual
tangents, and chart acceleration is cancelled by actual normal pairing. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix RealInnerProductSpace BigOperators
set_option backward.isDefEq.respectTransparency false

private theorem completedSaddleAnnulusGraphTransfer_jacobian_ne_zero
    {Φ : Coord → Coord} (hΦ : ContDiff ℝ ∞ Φ) {p : Coord}
    (hRank : Function.Injective (fderiv ℝ Φ p)) :
    (seamCoordinateJacobian Φ p).det ≠ 0 := by
  have hJinj : Function.Injective (seamCoordinateJacobian Φ p).mulVec := by
    intro v w hvw
    apply hRank
    simpa only [seamCoordinateJacobian_fderiv_apply hΦ] using hvw
  have hJUnit := Matrix.mulVec_injective_iff_isUnit.mp hJinj
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hJUnit)

/-- Private consuming calculation: derive curvature transfer through an
actual globally smooth chart. The open neighborhood of regularity is
constructed from the actual differential at the point. -/
private theorem completedSaddleAnnulusGraphTransfer_global_chart
    {F : Coord → Ambient} {U : Set Coord} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ F U)
    (hRankF : ∀ y ∈ U, Function.Injective (fderiv ℝ F y))
    {Φ : Coord → Coord} (hΦ : ContDiff ℝ ∞ Φ) {p : Coord}
    (hpU : Φ p ∈ U) (hRankΦ : Function.Injective (fderiv ℝ Φ p))
    (hNegative : gaussianCurvature (inducedMetric F) (Φ p) < 0) :
    gaussianCurvature (inducedMetric (F ∘ Φ)) p < 0 := by
  have hg := inducedMetric_smoothPositiveOn hF hU hRankF
  have hIsom := inducedMetric_isometricOn hF
  obtain ⟨n,hnUnit,hnTangents⟩ := exists_unit_normal_of_independent_tangents
    (fun i => coordPartial i F (Φ p)) (isometric_tangents_independent hg hIsom hpU)
  have hn : IsUnitNormalAt F n (Φ p) := by
    refine ⟨hnUnit,?_⟩
    intro v
    rw [fderiv_two_coordinates,inner_add_left,real_inner_smul_left,real_inner_smul_left,
      hnTangents 0,hnTangents 1]
    simp
  have hSecondNeg : (secondFundamental F n (Φ p)).det < 0 :=
    (negative_curvature_iff_second_form_det_neg hg hIsom hU hpU hn).mp hNegative
  have hJ := completedSaddleAnnulusGraphTransfer_jacobian_ne_zero hΦ hRankΦ
  let W : Set Coord := {q | Φ q ∈ U ∧ (seamCoordinateJacobian Φ q).det ≠ 0}
  have hW : IsOpen W := by
    exact (hU.preimage hΦ.continuous).inter
      (isClosed_singleton.isOpen_compl.preimage
        (seamCoordinateJacobian_continuous hΦ).matrix_det)
  have hpW : p ∈ W := ⟨hpU,hJ⟩
  have hFComp : ContDiffOn ℝ ∞ (F ∘ Φ) W :=
    hF.comp hΦ.contDiffOn (fun q hq => hq.1)
  have hRankComp : ∀ q ∈ W, Function.Injective (fderiv ℝ (F ∘ Φ) q) := by
    intro q hq
    have hdF := ((hF _ hq.1).contDiffAt (hU.mem_nhds hq.1)).differentiableAt (by simp)
    have hdΦ := hΦ.differentiable (by simp) q
    rw [fderiv_comp q hdF hdΦ]
    exact (hRankF _ hq.1).comp (seamCoordinateJacobian_differential_injective hΦ hq.2)
  have hdF := ((hF _ hpU).contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)
  have hdΦ := hΦ.differentiable (by simp) p
  have hnComp : IsUnitNormalAt (F ∘ Φ) n p := by
    refine ⟨hnUnit,?_⟩
    intro v
    rw [fderiv_comp p hdF hdΦ]
    exact hn.2 _
  have hHeightZero (i : Fin 2) : coordPartial i (height F n) (Φ p) = 0 := by
    unfold coordPartial
    rw [height_derivative_at_normal hF hU hpU hn]
    rfl
  have hHeightHessian : planarHessian (height F n) (Φ p) =
      secondFundamental F n (Φ p) := by
    ext i j
    exact second_partial_height hF hU hpU n i j
  have hSecondComp : secondFundamental (F ∘ Φ) n p =
      (seamCoordinateJacobian Φ p).transpose * secondFundamental F n (Φ p) *
        seamCoordinateJacobian Φ p := by
    ext i j
    change inner ℝ (coordPartial i (coordPartial j (F ∘ Φ)) p) n = _
    rw [← second_partial_height hFComp hW hpW n i j]
    change planarHessian (fun q => height F n (Φ q)) p i j = _
    rw [polarLocal_planarHessian_comp (height_smooth hF n) hU hΦ hpU]
    simp only [hHeightZero,zero_mul,Finset.sum_const_zero,add_zero,hHeightHessian]
  apply (negative_curvature_iff_second_form_det_neg
    (inducedMetric_smoothPositiveOn hFComp hW hRankComp)
    (inducedMetric_isometricOn hFComp) hW hpW hnComp).mpr
  rw [hSecondComp,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose]
  have hdetEq : (seamCoordinateJacobian Φ p).det * (secondFundamental F n (Φ p)).det *
      (seamCoordinateJacobian Φ p).det =
      (seamCoordinateJacobian Φ p).det^2 * (secondFundamental F n (Φ p)).det := by ring
  rw [hdetEq]
  exact mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hJ) hSecondNeg

/-- Actual intrinsic curvature signs for the same completed graphs in an
arbitrary actual curved smooth chart. Chart smoothness is needed only on
its ordinary open domain, and regularity only at the actual point. -/
theorem completedSaddleAnnulusGraphs_chart_gaussianCurvature_neg
    {G : Coord → ℝ} (e : OpenPartialHomeomorph Coord Coord) (dInfinity : ℝ)
    (hG : ContDiffOn ℝ ∞ G e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (heG : ∀ y ∈ e.source, e y = planarGradient G y)
    (hNeg : ∀ y ∈ e.source, (planarHessian G y).det < 0)
    {φ : Coord → Coord} {V : Set Coord} (hV : IsOpen V)
    (hφ : ContDiffOn ℝ ∞ φ V) (hMaps : MapsTo φ V e.target)
    {p : Coord} (hp : p ∈ V) (hRankφ : Function.Injective (fderiv ℝ φ p)) :
    gaussianCurvature (inducedMetric (completedSaddleAnnulusUpperGraph G e dInfinity ∘ φ)) p < 0 ∧
    gaussianCurvature (inducedMetric (completedSaddleAnnulusLowerGraph G e dInfinity ∘ φ)) p < 0 := by
  obtain ⟨Φ,hΦ,hGerm⟩ :=
    OAI.WeakMTWGlobalSupport.SmoothODE.exists_smooth_extension hV hφ hp
  have hValue : Φ p = φ p := hGerm.eq_of_nhds
  have hTarget : Φ p ∈ e.target := by rw [hValue]; exact hMaps hp
  have hRankΦ : Function.Injective (fderiv ℝ Φ p) := by
    rw [hGerm.fderiv_eq]
    exact hRankφ
  have hSmooth := completedSaddleAnnulusGraphs_contDiffOn e dInfinity hG hi
  have hActualNeg := completedSaddleAnnulusGraphs_gaussianCurvature_neg e dInfinity
    hG hi heG hNeg hTarget
  have hUpperNeg : gaussianCurvature
      (inducedMetric (completedSaddleAnnulusUpperGraph G e dInfinity ∘ Φ)) p < 0 :=
    completedSaddleAnnulusGraphTransfer_global_chart e.open_target hSmooth.1
      (fun y hy => (completedSaddleAnnulusGraphs_differential_injective e dInfinity hG hi hy).1)
      hΦ hTarget hRankΦ hActualNeg.1
  have hLowerNeg : gaussianCurvature
      (inducedMetric (completedSaddleAnnulusLowerGraph G e dInfinity ∘ Φ)) p < 0 :=
    completedSaddleAnnulusGraphTransfer_global_chart e.open_target hSmooth.2
      (fun y hy => (completedSaddleAnnulusGraphs_differential_injective e dInfinity hG hi hy).2)
      hΦ hTarget hRankΦ hActualNeg.2
  have hUpperGerm : (completedSaddleAnnulusUpperGraph G e dInfinity ∘ φ) =ᶠ[𝓝 p]
      (completedSaddleAnnulusUpperGraph G e dInfinity ∘ Φ) := by
    filter_upwards [hGerm] with q hq
    simp only [Function.comp_apply,hq]
  have hLowerGerm : (completedSaddleAnnulusLowerGraph G e dInfinity ∘ φ) =ᶠ[𝓝 p]
      (completedSaddleAnnulusLowerGraph G e dInfinity ∘ Φ) := by
    filter_upwards [hGerm] with q hq
    simp only [Function.comp_apply,hq]
  rw [gaussianCurvature_eq_of_eventuallyEq (inducedMetric_eventuallyEq hUpperGerm),
    gaussianCurvature_eq_of_eventuallyEq (inducedMetric_eventuallyEq hLowerGerm)]
  exact ⟨hUpperNeg,hLowerNeg⟩

theorem completedSaddleAnnulusUpperGraph_chart_gaussianCurvature_neg
    {G : Coord → ℝ} (e : OpenPartialHomeomorph Coord Coord) (dInfinity : ℝ)
    (hG : ContDiffOn ℝ ∞ G e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (heG : ∀ y ∈ e.source, e y = planarGradient G y)
    (hNeg : ∀ y ∈ e.source, (planarHessian G y).det < 0)
    {φ : Coord → Coord} {V : Set Coord} (hV : IsOpen V)
    (hφ : ContDiffOn ℝ ∞ φ V) (hMaps : MapsTo φ V e.target)
    {p : Coord} (hp : p ∈ V) (hRankφ : Function.Injective (fderiv ℝ φ p)) :
    gaussianCurvature (inducedMetric (completedSaddleAnnulusUpperGraph G e dInfinity ∘ φ)) p < 0 :=
  (completedSaddleAnnulusGraphs_chart_gaussianCurvature_neg e dInfinity
    hG hi heG hNeg hV hφ hMaps hp hRankφ).1

theorem completedSaddleAnnulusLowerGraph_chart_gaussianCurvature_neg
    {G : Coord → ℝ} (e : OpenPartialHomeomorph Coord Coord) (dInfinity : ℝ)
    (hG : ContDiffOn ℝ ∞ G e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (heG : ∀ y ∈ e.source, e y = planarGradient G y)
    (hNeg : ∀ y ∈ e.source, (planarHessian G y).det < 0)
    {φ : Coord → Coord} {V : Set Coord} (hV : IsOpen V)
    (hφ : ContDiffOn ℝ ∞ φ V) (hMaps : MapsTo φ V e.target)
    {p : Coord} (hp : p ∈ V) (hRankφ : Function.Injective (fderiv ℝ φ p)) :
    gaussianCurvature (inducedMetric (completedSaddleAnnulusLowerGraph G e dInfinity ∘ φ)) p < 0 :=
  (completedSaddleAnnulusGraphs_chart_gaussianCurvature_neg e dInfinity
    hG hi heG hNeg hV hφ hMaps hp hRankφ).2

end
end TightVer401
