import TightVer401.RevolutionEndBoundaryMetricSmooth

namespace TightVer401
noncomputable section
open Set Filter Bundle ContinuousLinearMap OAI.SmoothLocal.Geometry
open scoped Manifold ContDiff Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
 theorem revolutionEndBoundaryInducedInner_coordinate_germ (q : ℝ → ℝ) (p₀ : RevolutionClosedEnd H) :
    (fun p => (trivializationAt ((ℝ × EuclideanSpace ℝ (Fin 1)) →L[ℝ] (ℝ × EuclideanSpace ℝ (Fin 1)) →L[ℝ] ℝ)
      (fun p : RevolutionClosedEnd H => TangentSpace revolutionEndBoundaryModel p →L[ℝ]
        TangentSpace revolutionEndBoundaryModel p →L[ℝ] ℝ) p₀
      ⟨p, revolutionEndBoundaryInducedInner q p⟩).2) =ᶠ[𝓝 p₀] revolutionEndBoundaryInnerCoordinates q p₀ := by
  filter_upwards [(chartAt (ModelProd ℝ (EuclideanHalfSpace 1)) p₀).open_source.mem_nhds
    (mem_chart_source (ModelProd ℝ (EuclideanHalfSpace 1)) p₀)] with p hp
  have hT : p ∈ (trivializationAt (ℝ × EuclideanSpace ℝ (Fin 1)) (TangentSpace revolutionEndBoundaryModel) p₀).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hp
  have hR : p ∈ (trivializationAt ℝ (Bundle.Trivial (RevolutionClosedEnd H) ℝ) p₀).baseSet := by
    simp [Trivial.fiberBundle_trivializationAt']
  have hA (v : ℝ × EuclideanSpace ℝ (Fin 1)) : revolutionEndBoundaryDerivativeCoordinates q p₀ p v =
      mfderiv revolutionEndBoundaryModel 𝓘(ℝ, Ambient) (revolutionEndCircle q H) p
        ((trivializationAt (ℝ × EuclideanSpace ℝ (Fin 1)) (TangentSpace revolutionEndBoundaryModel) p₀).symm p v) := by
    rw [revolutionEndBoundaryDerivativeCoordinates, inTangentCoordinates, inCoordinates,
      TangentBundle.continuousLinearMapAt_model_space]
    change mfderiv revolutionEndBoundaryModel 𝓘(ℝ, Ambient) (revolutionEndCircle q H) p
      ((trivializationAt (ℝ × EuclideanSpace ℝ (Fin 1)) (TangentSpace revolutionEndBoundaryModel) p₀).symmL ℝ p v) = _
    rw [(trivializationAt (ℝ × EuclideanSpace ℝ (Fin 1)) (TangentSpace revolutionEndBoundaryModel) p₀).symmL_apply hT]
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  rw [hom_trivializationAt_apply, inCoordinates_apply_eq₂ hT hT hR]
  simp only [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization,
    LinearMap.id_coe, id_eq]
  rw [revolutionEndBoundaryInducedInner_apply]
  change inner ℝ _ _ = inner ℝ (revolutionEndBoundaryDerivativeCoordinates q p₀ p v)
    (revolutionEndBoundaryDerivativeCoordinates q p₀ p w)
  rw [hA v, hA w]

 theorem revolutionEndBoundaryInducedInner_section_contMDiff {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q) :
    ContMDiff revolutionEndBoundaryModel
      (revolutionEndBoundaryModel.prod 𝓘(ℝ, (ℝ × EuclideanSpace ℝ (Fin 1)) →L[ℝ] (ℝ × EuclideanSpace ℝ (Fin 1)) →L[ℝ] ℝ)) ∞
      (fun p : RevolutionClosedEnd H => TotalSpace.mk' ((ℝ × EuclideanSpace ℝ (Fin 1)) →L[ℝ] (ℝ × EuclideanSpace ℝ (Fin 1)) →L[ℝ] ℝ) p
        (revolutionEndBoundaryInducedInner q p)) := by
  intro p
  rw [contMDiffAt_section]
  exact (revolutionEndBoundaryInnerCoordinates_contMDiffAt hq p).congr_of_eventuallyEq
    (revolutionEndBoundaryInducedInner_coordinate_germ q p)

 def revolutionEndBoundaryContMDiffRiemannianMetric {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    (hpos : ∀ z ∈ Ici H, 0 < q z) :
    ContMDiffRiemannianMetric revolutionEndBoundaryModel ∞ (ℝ × EuclideanSpace ℝ (Fin 1))
      (fun p : RevolutionClosedEnd H => TangentSpace revolutionEndBoundaryModel p) where
  inner := revolutionEndBoundaryInducedInner q
  symm := (revolutionEndBoundaryRiemannianMetric hq hpos).symm
  pos := (revolutionEndBoundaryRiemannianMetric hq hpos).pos
  isVonNBounded := (revolutionEndBoundaryRiemannianMetric hq hpos).isVonNBounded
  contMDiff := revolutionEndBoundaryInducedInner_section_contMDiff hq

theorem revolutionEndBoundaryRiemannianMetric_isContMDiff {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    (hpos : ∀ z ∈ Ici H, 0 < q z) :
    letI : RiemannianBundle (fun p : RevolutionClosedEnd H => TangentSpace revolutionEndBoundaryModel p) :=
      ⟨revolutionEndBoundaryRiemannianMetric hq hpos⟩
    IsContMDiffRiemannianBundle revolutionEndBoundaryModel ∞ (ℝ × EuclideanSpace ℝ (Fin 1))
      (fun p : RevolutionClosedEnd H => TangentSpace revolutionEndBoundaryModel p) := by
  letI : RiemannianBundle (fun p : RevolutionClosedEnd H => TangentSpace revolutionEndBoundaryModel p) :=
    ⟨revolutionEndBoundaryRiemannianMetric hq hpos⟩
  exact ⟨revolutionEndBoundaryInducedInner q, revolutionEndBoundaryInducedInner_section_contMDiff hq,
    fun _ _ _ => rfl⟩

theorem revolutionEndBoundaryRiemannianMetric_isContinuous {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    (hpos : ∀ z ∈ Ici H, 0 < q z) :
    letI : RiemannianBundle (fun p : RevolutionClosedEnd H => TangentSpace revolutionEndBoundaryModel p) :=
      ⟨revolutionEndBoundaryRiemannianMetric hq hpos⟩
    IsContinuousRiemannianBundle (ℝ × EuclideanSpace ℝ (Fin 1))
      (fun p : RevolutionClosedEnd H => TangentSpace revolutionEndBoundaryModel p) := by
  letI : RiemannianBundle (fun p : RevolutionClosedEnd H => TangentSpace revolutionEndBoundaryModel p) :=
    ⟨revolutionEndBoundaryRiemannianMetric hq hpos⟩
  exact ⟨revolutionEndBoundaryInducedInner q, (revolutionEndBoundaryInducedInner_section_contMDiff hq).continuous,
    fun _ _ _ => rfl⟩

end
end TightVer401



