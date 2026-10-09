import TightVer401.QuadraticRadialFillingGlobalContract
import TightVer401.QuadraticRadialFillingImageAssembly
import TightVer401.AnnularDegreeGradient
import TightVer401.QuadraticRadialFillingDegreeData
import TightVer401.QuadraticRadialFillingGlobalOverlapContract

/-! Actual image/injectivity to smooth gradient inverse assembly for the
same punctured filling. The ordinary full producer is assembled below. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

theorem quadraticRadialFillingGlobalGradientTarget_eq (Γ : ℂ ≃ₜ ℂ) (L : ℝ) :
    quadraticRadialFillingGlobalGradientTarget Γ L =
      {y : Coord | planarRadius y < L} \ seamComplexCoord '' (Γ '' Metric.closedBall (0:ℂ) 1) := by
  ext y
  constructor
  · rintro ⟨z,⟨hz,hzJ⟩,rfl⟩
    refine ⟨?_,?_⟩
    · change planarRadius (seamComplexCoord z) < L
      rw [quadraticRadialFillingRadius_complex]
      simpa only [Metric.mem_ball,dist_zero_right] using hz
    · rintro ⟨w,hw,heq⟩
      exact hzJ (seamComplexCoord.injective heq ▸ hw)
  · rintro ⟨hy,hyJ⟩
    refine ⟨seamComplexCoord.symm y,⟨?_,?_⟩,seamComplexCoord.apply_symm_apply y⟩
    · rw [Metric.mem_ball,dist_zero_right,← quadraticRadialFillingRadius_complex,
        seamComplexCoord.apply_symm_apply]
      exact hy
    · intro hw
      exact hyJ ⟨seamComplexCoord.symm y,hw,seamComplexCoord.apply_symm_apply y⟩

theorem quadraticRadialFillingPuncturedDisk_isOpen (S : ℝ) :
    IsOpen (quadraticRadialFillingPuncturedDisk S) :=
  quadraticRadialFilling_openAnnulus_isOpen 0 S

/-- Actual whole image and actual injection construct the genuine smooth
gradient inverse; its derivative rank is derived from the actual Hessian. -/
theorem quadraticRadialFilling_exists_smooth_gradient_inverse_of_image
    {H : Coord → ℝ} {S L : ℝ} (Γ : ℂ ≃ₜ ℂ)
    (hH : ContDiffOn ℝ ∞ H (quadraticRadialFillingPuncturedDisk S))
    (hNeg : ∀ p ∈ quadraticRadialFillingPuncturedDisk S, (planarHessian H p).det < 0)
    (hInj : InjOn (planarGradient H) (quadraticRadialFillingPuncturedDisk S))
    (hImage : planarGradient H '' quadraticRadialFillingPuncturedDisk S =
      quadraticRadialFillingGlobalGradientTarget Γ L) :
    ∃ e : OpenPartialHomeomorph Coord Coord,
      e.source = quadraticRadialFillingPuncturedDisk S ∧
      e.target = quadraticRadialFillingGlobalGradientTarget Γ L ∧
      (e : Coord → Coord) = planarGradient H ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  have hOpen := quadraticRadialFillingPuncturedDisk_isOpen S
  have hJac : ∀ p ∈ quadraticRadialFillingPuncturedDisk S,
      annularJacobian (planarGradient H) p ≠ 0 := by
    intro p hp
    rw [annularGradientJacobian_eq_hessian_det hH hOpen hp]
    exact ne_of_lt (hNeg p hp)
  have hUnique : ∀ y ∈ planarGradient H '' quadraticRadialFillingPuncturedDisk S,
      ∃! x, x ∈ quadraticRadialFillingPuncturedDisk S ∧ planarGradient H x = y := by
    rintro y ⟨x,hx,rfl⟩
    refine ⟨x,⟨hx,rfl⟩,?_⟩
    intro z hz
    exact hInj hz.1 hx hz.2
  obtain ⟨e,hSource,hTarget,he,hi⟩ := annular_exists_smooth_image_inverse hOpen
    (planarGradient_contDiffOn hH hOpen) hJac hUnique
  exact ⟨e,hSource,hTarget.trans hImage,he,hi⟩

/-- Full ordinary incoming quadratic filling with its genuine global smooth
gradient inverse. The actual reversed fixed-band degree application is
combined with the exact scalar inner germ, not supplied as a premise. -/
theorem exists_quadratic_radial_filling_global_gradient_with_overlap :
    QuadraticRadialFillingGlobalGradientOverlapClaim := by
  intro R hR F U N hU hN hCircleU hCircleN hF hNegF hRadial hTangential hJordan M₀ η hη
  obtain ⟨S,B,M,H,Γ,hRS,hB,hM₀,hM,hH,hNeg,hBandD,hExterior,hInner,hOuter,
    hTrace,hOuterInj,hOrigin,hNested,hPosition,hBound,hEscape⟩ :=
    exists_quadratic_radial_filling_boundary_data_of_jordan_image hR hU hN hCircleU
      hCircleN hF hNegF hRadial hTangential hJordan M₀ hη
  have hS : 0 < S := hR.trans hRS
  have hρ : 0 < R/4 := by positivity
  have hρHalf : R/4 < R/2 := by linarith
  have hρS : R/4 < S := by linarith
  have hD : IsOpen (quadraticRadialFillingDomain R U) :=
    (isOpen_lt continuous_const quadraticRadialFillingRadius_continuous).inter
      ((isOpen_lt quadraticRadialFillingRadius_continuous continuous_const).union hU)
  have hPunctureD : quadraticRadialFillingPuncturedDisk S ⊆
      quadraticRadialFillingDomain R U := by
    intro x hx
    by_cases hr : planarRadius x < R
    · exact ⟨hx.1,Or.inl hr⟩
    · exact hBandD ⟨by linarith [le_of_not_gt hr],hx.2.le⟩
  have hBandNeg : ∀ x ∈ quadraticRadialFillingOpenAnnulus (R/4) S,
      (planarHessian H x).det < 0 := by
    intro x hx
    exact hNeg x (hBandD ⟨hx.1.le,hx.2.le⟩)
  obtain ⟨hBandImage,hBandInj⟩ := quadraticRadialFillingDegree_closed_band_image_and_injOn
    hR hM hρ hρHalf hρS Γ hD hH hBandD hBandNeg hInner hOuterInj hTrace hOrigin hNested
      (quadraticRadialFillingDegree_radial_unit_positive hS hPosition)
  have hPartition : seamComplexCoord '' (Γ '' Metric.closedBall (0:ℂ) 1) =
      seamComplexCoord '' (Γ '' Metric.ball (0:ℂ) 1) ∪
        seamComplexCoord '' (Γ '' Metric.sphere (0:ℂ) 1) := by
    rw [← image_union,← image_union]
    congr 1
    congr 1
    ext z
    simp only [Metric.mem_closedBall,Metric.mem_ball,Metric.mem_sphere,mem_union,
      le_iff_lt_or_eq]
  have hJordanBound : seamComplexCoord '' (Γ '' Metric.closedBall (0:ℂ) 1) ⊆
      {y : Coord | planarRadius y < M*(R-R/4)} := by
    rintro y ⟨z,hz,rfl⟩
    change planarRadius (seamComplexCoord z) < M*(R-R/4)
    rw [quadraticRadialFillingRadius_complex]
    simpa only [Metric.mem_ball,dist_zero_right] using hNested hz
  have hOuterImage : planarGradient H '' quadraticRadialFillingRadiusLevel S =
      seamComplexCoord '' (Γ '' Metric.sphere (0:ℂ) 1) := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      obtain ⟨θ,rfl⟩ := quadraticRadialFilling_radiusLevel_exists_polar hS hx
      refine ⟨quadraticRadialFillingGradientComplexTrace H S θ,?_,?_⟩
      · rw [← hTrace]
        exact mem_range_self θ
      · exact quadraticRadialFillingCoord_complex _
    · rintro ⟨z,hz,rfl⟩
      rw [← hTrace] at hz
      obtain ⟨θ,rfl⟩ := hz
      refine ⟨saddlePolarChart ![S,θ],?_,?_⟩
      · exact angularDescent_radius_polar (by simpa using hS)
      · exact (quadraticRadialFillingCoord_complex _).symm
  have hFull := quadraticRadialFilling_puncturedDisk_image_and_injOn_of_degreeBand
    hR hM hρ hρHalf.le hρS hInner hPartition hJordanBound hBandInj hBandImage hOuterImage
  have hImage : planarGradient H '' quadraticRadialFillingPuncturedDisk S =
      quadraticRadialFillingGlobalGradientTarget Γ (M*R) := by
    rw [quadraticRadialFillingGlobalGradientTarget_eq]
    exact hFull.1
  obtain ⟨e,hes,het,hef,hei⟩ := quadraticRadialFilling_exists_smooth_gradient_inverse_of_image
    Γ (hH.mono hPunctureD) (fun x hx => hNeg x (hPunctureD hx)) hFull.2 hImage
  have hNestedMR : Γ '' Metric.closedBall (0:ℂ) 1 ⊆ Metric.ball (0:ℂ) (M*R) := by
    intro z hz
    have hC : M*(R-R/4) < M*R := mul_lt_mul_of_pos_left (by linarith) hM
    have hn : ‖z‖ < M*(R-R/4) := by
      simpa only [Metric.mem_ball,dist_zero_right] using hNested hz
    simpa only [Metric.mem_ball,dist_zero_right] using hn.trans hC
  have hOverlap := quadraticRadialFilling_exists_retained_inverse_overlap
    hR hRS hU hBandD hOuter e hes hef
  exact ⟨S,M,H,Γ,e,hRS,hM₀,hM,hH,hNeg,hPunctureD,hExterior,hInner,hOuter,
    hTrace,hOrigin,hNestedMR,hes,het,hef,hei,hOverlap⟩

/-- The full ordinary filling producer with the original exact interface. -/
theorem exists_quadratic_radial_filling_global_gradient :
    QuadraticRadialFillingGlobalGradientClaim :=
  quadraticRadialFillingGlobalGradientClaim_of_overlap
    exists_quadratic_radial_filling_global_gradient_with_overlap

end
end TightVer401
