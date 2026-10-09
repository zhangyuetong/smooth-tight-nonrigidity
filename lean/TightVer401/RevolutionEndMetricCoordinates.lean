import TightVer401.RevolutionEndRiemannianSmooth

namespace TightVer401
noncomputable section
open Set Filter Bundle ContinuousLinearMap OAI.SmoothLocal.Geometry
open scoped Manifold ContDiff Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
 theorem revolutionEndInducedInner_coordinate_germ (q : ℝ → ℝ) (p₀ : RevolutionCylinder) :
    (fun p => (trivializationAt ((ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] ℝ)
      (fun p : RevolutionCylinder => TangentSpace revolutionCylinderModel p →L[ℝ]
        TangentSpace revolutionCylinderModel p →L[ℝ] ℝ) p₀
      ⟨p, revolutionEndInducedInner q p⟩).2) =ᶠ[𝓝 p₀] revolutionEndInnerCoordinates q p₀ := by
  filter_upwards [(chartAt (ModelProd ℝ ℝ) p₀).open_source.mem_nhds
    (mem_chart_source (ModelProd ℝ ℝ) p₀)] with p hp
  have hT : p ∈ (trivializationAt (ℝ × ℝ) (TangentSpace revolutionCylinderModel) p₀).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hp
  have hR : p ∈ (trivializationAt ℝ (Bundle.Trivial RevolutionCylinder ℝ) p₀).baseSet := by
    simp [Trivial.fiberBundle_trivializationAt']
  have hA (v : ℝ × ℝ) : revolutionEndDerivativeCoordinates q p₀ p v =
      mfderiv revolutionCylinderModel 𝓘(ℝ, Ambient) (revolutionEndCircleFull q) p
        ((trivializationAt (ℝ × ℝ) (TangentSpace revolutionCylinderModel) p₀).symm p v) := by
    rw [revolutionEndDerivativeCoordinates, inTangentCoordinates, inCoordinates,
      TangentBundle.continuousLinearMapAt_model_space]
    change mfderiv revolutionCylinderModel 𝓘(ℝ, Ambient) (revolutionEndCircleFull q) p
      ((trivializationAt (ℝ × ℝ) (TangentSpace revolutionCylinderModel) p₀).symmL ℝ p v) = _
    rw [(trivializationAt (ℝ × ℝ) (TangentSpace revolutionCylinderModel) p₀).symmL_apply hT]
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  rw [hom_trivializationAt_apply, inCoordinates_apply_eq₂ hT hT hR]
  simp only [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization,
    LinearMap.id_coe, id_eq]
  rw [revolutionEndInducedInner_apply]
  change inner ℝ _ _ = inner ℝ (revolutionEndDerivativeCoordinates q p₀ p v)
    (revolutionEndDerivativeCoordinates q p₀ p w)
  rw [hA v, hA w]

 theorem revolutionEndInducedInner_section_contMDiff {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q) :
    ContMDiff revolutionCylinderModel
      (revolutionCylinderModel.prod 𝓘(ℝ, (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] ℝ)) ∞
      (fun p : RevolutionCylinder => TotalSpace.mk' ((ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] ℝ) p
        (revolutionEndInducedInner q p)) := by
  intro p
  rw [contMDiffAt_section]
  exact (revolutionEndInnerCoordinates_contMDiffAt hq p).congr_of_eventuallyEq
    (revolutionEndInducedInner_coordinate_germ q p)

 def revolutionEndContMDiffRiemannianMetric {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    (hpos : ∀ z, 0 < q z) :
    ContMDiffRiemannianMetric revolutionCylinderModel ∞ (ℝ × ℝ)
      (fun p : RevolutionCylinder => TangentSpace revolutionCylinderModel p) where
  inner := revolutionEndInducedInner q
  symm := (revolutionEndRiemannianMetric hq hpos).symm
  pos := (revolutionEndRiemannianMetric hq hpos).pos
  isVonNBounded := (revolutionEndRiemannianMetric hq hpos).isVonNBounded
  contMDiff := revolutionEndInducedInner_section_contMDiff hq

theorem revolutionEndRiemannianMetric_isContMDiff {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    (hpos : ∀ z, 0 < q z) :
    letI : RiemannianBundle (fun p : RevolutionCylinder => TangentSpace revolutionCylinderModel p) :=
      ⟨revolutionEndRiemannianMetric hq hpos⟩
    IsContMDiffRiemannianBundle revolutionCylinderModel ∞ (ℝ × ℝ)
      (fun p : RevolutionCylinder => TangentSpace revolutionCylinderModel p) := by
  letI : RiemannianBundle (fun p : RevolutionCylinder => TangentSpace revolutionCylinderModel p) :=
    ⟨revolutionEndRiemannianMetric hq hpos⟩
  exact ⟨revolutionEndInducedInner q, revolutionEndInducedInner_section_contMDiff hq,
    fun _ _ _ => rfl⟩

theorem revolutionEndRiemannianMetric_isContinuous {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    (hpos : ∀ z, 0 < q z) :
    letI : RiemannianBundle (fun p : RevolutionCylinder => TangentSpace revolutionCylinderModel p) :=
      ⟨revolutionEndRiemannianMetric hq hpos⟩
    IsContinuousRiemannianBundle (ℝ × ℝ)
      (fun p : RevolutionCylinder => TangentSpace revolutionCylinderModel p) := by
  letI : RiemannianBundle (fun p : RevolutionCylinder => TangentSpace revolutionCylinderModel p) :=
    ⟨revolutionEndRiemannianMetric hq hpos⟩
  exact ⟨revolutionEndInducedInner q, (revolutionEndInducedInner_section_contMDiff hq).continuous,
    fun _ _ _ => rfl⟩

end
end TightVer401

