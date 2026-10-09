import TightVer401.RevolutionEndRiemannianNorm
import TightVer401.RevolutionEndPathELength

namespace TightVer401
noncomputable section
open Set Filter Bundle Manifold MeasureTheory OAI.SmoothLocal.Geometry
open scoped Manifold ContDiff Topology Bundle
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

 theorem revolutionEnd_native_pathELength_eq_image {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    (hpos : ∀ z, 0 < q z) {c : ℝ → RevolutionCylinder} {A B : ℝ}
    (hc : ContMDiffOn 𝓘(ℝ, ℝ) revolutionCylinderModel 1 c (Icc A B)) :
    letI : RiemannianBundle (fun p : RevolutionCylinder => TangentSpace revolutionCylinderModel p) :=
      ⟨revolutionEndRiemannianMetric hq hpos⟩
    pathELength revolutionCylinderModel c A B =
      pathELength 𝓘(ℝ, Ambient) (revolutionEndCircleFull q ∘ c) A B := by
  letI : RiemannianBundle (fun p : RevolutionCylinder => TangentSpace revolutionCylinderModel p) :=
    ⟨revolutionEndRiemannianMetric hq hpos⟩
  rw [pathELength_eq_lintegral_mfderiv_Ioo, pathELength_eq_lintegral_mfderiv_Ioo]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have hcd := ((hc t ⟨ht.1.le, ht.2.le⟩).contMDiffAt (Icc_mem_nhds ht.1 ht.2)).mdifferentiableAt (by simp)
  have hXd := (revolutionEndCircleFull_contMDiff hq (c t)).mdifferentiableAt (by simp)
  change ‖mfderiv 𝓘(ℝ, ℝ) revolutionCylinderModel c t 1‖ₑ =
    ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Ambient) (revolutionEndCircleFull q ∘ c) t 1‖ₑ
  have hchain :
      (show Ambient from mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Ambient) (revolutionEndCircleFull q ∘ c) t 1) =
      mfderiv revolutionCylinderModel 𝓘(ℝ, Ambient) (revolutionEndCircleFull q) (c t)
        (mfderiv 𝓘(ℝ, ℝ) revolutionCylinderModel c t 1) :=
    mfderiv_comp_apply t hXd hcd 1
  have hnorm := revolutionEndRiemannianMetric_norm hq hpos (c t)
    (mfderiv 𝓘(ℝ, ℝ) revolutionCylinderModel c t 1)
  have he :
      ‖mfderiv 𝓘(ℝ, ℝ) revolutionCylinderModel c t 1‖ₑ =
      ‖show Ambient from mfderiv revolutionCylinderModel 𝓘(ℝ, Ambient)
        (revolutionEndCircleFull q) (c t) (mfderiv 𝓘(ℝ, ℝ) revolutionCylinderModel c t 1)‖ₑ :=
    enorm_eq_iff_norm_eq.mpr hnorm
  exact he.trans ((congrArg (fun v : Ambient => ‖v‖ₑ) hchain).symm.trans
    enorm_tangentSpace_vectorSpace.symm)

 theorem revolutionEnd_native_height_edist_le_pathELength {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    (hpos : ∀ z, 0 < q z) {c : ℝ → RevolutionCylinder} {A B : ℝ}
    (hc : ContMDiffOn 𝓘(ℝ, ℝ) revolutionCylinderModel 1 c (Icc A B)) (hAB : A ≤ B) :
    letI : RiemannianBundle (fun p : RevolutionCylinder => TangentSpace revolutionCylinderModel p) :=
      ⟨revolutionEndRiemannianMetric hq hpos⟩
    edist (c A).2 (c B).2 ≤ pathELength revolutionCylinderModel c A B := by
  letI : RiemannianBundle (fun p : RevolutionCylinder => TangentSpace revolutionCylinderModel p) :=
    ⟨revolutionEndRiemannianMetric hq hpos⟩
  rw [revolutionEnd_native_pathELength_eq_image hq hpos hc]
  exact revolutionEndCircleCurve_height_edist_le_pathELength hq hc hAB

end
end TightVer401


