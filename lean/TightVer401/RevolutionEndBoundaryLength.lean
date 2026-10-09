import TightVer401.RevolutionEndBoundaryMetricNorm
import TightVer401.RevolutionEndPathELength

namespace TightVer401
noncomputable section
open Set Filter Bundle Manifold MeasureTheory OAI.SmoothLocal.Geometry
open scoped Manifold ContDiff Topology Bundle
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

 theorem revolutionEnd_boundary_pathELength_eq_image {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    (hpos : ∀ z ∈ Ici H, 0 < q z) {c : ℝ → RevolutionClosedEnd H} {A B : ℝ}
    (hc : ContMDiffOn 𝓘(ℝ, ℝ) revolutionEndBoundaryModel 1 c (Icc A B)) :
    letI : RiemannianBundle (fun p : RevolutionClosedEnd H => TangentSpace revolutionEndBoundaryModel p) :=
      ⟨revolutionEndBoundaryRiemannianMetric hq hpos⟩
    pathELength revolutionEndBoundaryModel c A B =
      pathELength 𝓘(ℝ, Ambient) (revolutionEndCircle q H ∘ c) A B := by
  letI : RiemannianBundle (fun p : RevolutionClosedEnd H => TangentSpace revolutionEndBoundaryModel p) :=
    ⟨revolutionEndBoundaryRiemannianMetric hq hpos⟩
  rw [pathELength_eq_lintegral_mfderiv_Ioo, pathELength_eq_lintegral_mfderiv_Ioo]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have hcd := ((hc t ⟨ht.1.le, ht.2.le⟩).contMDiffAt (Icc_mem_nhds ht.1 ht.2)).mdifferentiableAt (by simp)
  have hXd := (revolutionEndCircle_boundary_contMDiff hq H (c t)).mdifferentiableAt (by simp)
  change ‖mfderiv 𝓘(ℝ, ℝ) revolutionEndBoundaryModel c t 1‖ₑ =
    ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Ambient) (revolutionEndCircle q H ∘ c) t 1‖ₑ
  have hchain :
      (show Ambient from mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Ambient) (revolutionEndCircle q H ∘ c) t 1) =
      mfderiv revolutionEndBoundaryModel 𝓘(ℝ, Ambient) (revolutionEndCircle q H) (c t)
        (mfderiv 𝓘(ℝ, ℝ) revolutionEndBoundaryModel c t 1) :=
    mfderiv_comp_apply t hXd hcd 1
  have hnorm := revolutionEndBoundaryRiemannianMetric_norm hq hpos (c t)
    (mfderiv 𝓘(ℝ, ℝ) revolutionEndBoundaryModel c t 1)
  have he :
      ‖mfderiv 𝓘(ℝ, ℝ) revolutionEndBoundaryModel c t 1‖ₑ =
      ‖show Ambient from mfderiv revolutionEndBoundaryModel 𝓘(ℝ, Ambient)
        (revolutionEndCircle q H) (c t) (mfderiv 𝓘(ℝ, ℝ) revolutionEndBoundaryModel c t 1)‖ₑ :=
    enorm_eq_iff_norm_eq.mpr hnorm
  exact he.trans ((congrArg (fun v : Ambient => ‖v‖ₑ) hchain).symm.trans
    enorm_tangentSpace_vectorSpace.symm)

 theorem revolutionEnd_boundary_height_edist_le_pathELength {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    (hpos : ∀ z ∈ Ici H, 0 < q z) {c : ℝ → RevolutionClosedEnd H} {A B : ℝ}
    (hc : ContMDiffOn 𝓘(ℝ, ℝ) revolutionEndBoundaryModel 1 c (Icc A B)) (hAB : A ≤ B) :
    letI : RiemannianBundle (fun p : RevolutionClosedEnd H => TangentSpace revolutionEndBoundaryModel p) :=
      ⟨revolutionEndBoundaryRiemannianMetric hq hpos⟩
    edist ((c A).2 : ℝ) ((c B).2 : ℝ) ≤ pathELength revolutionEndBoundaryModel c A B := by
  letI : RiemannianBundle (fun p : RevolutionClosedEnd H => TangentSpace revolutionEndBoundaryModel p) :=
    ⟨revolutionEndBoundaryRiemannianMetric hq hpos⟩
  rw [revolutionEnd_boundary_pathELength_eq_image hq hpos hc]
  have himg : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, Ambient) 1
      (revolutionEndCircle q H ∘ c) (Icc A B) :=
    ((revolutionEndCircle_boundary_contMDiff hq H).of_le (by simp)).comp_contMDiffOn hc
  have h := revolution_ambientCurve_height_edist_le_pathELength
    (contMDiffOn_iff_contDiffOn.mp himg) hAB
  simpa only [Function.comp_apply, revolutionEndCircle_height] using h

end
end TightVer401




