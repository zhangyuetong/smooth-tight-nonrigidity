import TightVer401.SphereCharts
import TightVer401.SphereSupportTransition

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology RealInnerProductSpace

def hemisphereHeight (w : Ambient) (hw : w ≠ 0) (hu : ‖w‖ = 1)
    (H : RoundSphere → ℝ) : Coord → ℝ := fun p => H (sphereHemispherePoint w hw hu p)

def hemisphereSupport (w : Ambient) (hw : w ≠ 0) (hu : ‖w‖ = 1)
    (H : RoundSphere → ℝ) : Coord → Ambient :=
  sphereSupportMap (inducedMetric (sphereHemisphere w hw)) (sphereHemisphere w hw)
    (hemisphereHeight w hw hu H)

theorem hemisphereSupport_agrees (w₁ w₂ : Ambient) (hw₁ : w₁ ≠ 0) (hw₂ : w₂ ≠ 0)
    (hu₁ : ‖w₁‖ = 1) (hu₂ : ‖w₂‖ = 1) (H : RoundSphere → ℝ)
    (hH₂ : ContDiff ℝ ∞ (hemisphereHeight w₂ hw₂ hu₂ H))
    {p : Coord} (hp : 0 < inner ℝ w₂ (sphereHemisphere w₁ hw₁ p)) :
    hemisphereSupport w₁ hw₁ hu₁ H p = hemisphereSupport w₂ hw₂ hu₂ H
      (sphereHemisphereInverse w₂ hw₂ (sphereHemisphere w₁ hw₁ p)) := by
  let C : Coord → Coord := fun q => sphereHemisphereInverse w₂ hw₂ (sphereHemisphere w₁ hw₁ q)
  have hV : IsOpen {q | 0 < inner ℝ w₂ (sphereHemisphere w₁ hw₁ q)} :=
    isOpen_lt continuous_const (continuous_const.inner (sphereHemisphere_contDiff w₁ hw₁ hu₁).continuous)
  have hQeq : sphereHemisphere w₁ hw₁ =ᶠ[𝓝 p] (fun q => sphereHemisphere w₂ hw₂ (C q)) := by
    filter_upwards [hV.mem_nhds hp] with q hq
    exact (sphereHemisphere_transition_eq w₁ w₂ hw₁ hw₂ hu₁ hu₂ hq).symm
  have hHeq : hemisphereHeight w₁ hw₁ hu₁ H =ᶠ[𝓝 p]
      (fun q => hemisphereHeight w₂ hw₂ hu₂ H (C q)) := by
    filter_upwards [hQeq] with q hq
    change H (sphereHemispherePoint w₁ hw₁ hu₁ q) =
      H (sphereHemispherePoint w₂ hw₂ hu₂ (C q))
    exact congrArg H (Subtype.ext hq)
  have hg₁ := sphereHemisphere_metric w₁ hw₁ hu₁
  have hg₂ := sphereHemisphere_metric w₂ hw₂ hu₂
  have hC : DifferentiableAt ℝ C p :=
    ((sphereHemisphereInverse_contDiffAt w₂ hw₂ hp).comp p
      (sphereHemisphere_contDiff w₁ hw₁ hu₁).contDiffAt).differentiableAt (by simp)
  have hunit₁ : ∀ q ∈ univ, inner ℝ (sphereHemisphere w₁ hw₁ q) (sphereHemisphere w₁ hw₁ q) = 1 := by
    intro q _
    rw [real_inner_self_eq_norm_sq, sphereHemisphere_norm w₁ hw₁ hu₁, one_pow]
  have hunit₂ : ∀ q ∈ univ, inner ℝ (sphereHemisphere w₂ hw₂ q) (sphereHemisphere w₂ hw₂ q) = 1 := by
    intro q _
    rw [real_inner_self_eq_norm_sq, sphereHemisphere_norm w₂ hw₂ hu₂, one_pow]
  change sphereSupportMap (inducedMetric (sphereHemisphere w₁ hw₁)) (sphereHemisphere w₁ hw₁)
    (hemisphereHeight w₁ hw₁ hu₁ H) p =
    sphereSupportMap (inducedMetric (sphereHemisphere w₂ hw₂)) (sphereHemisphere w₂ hw₂)
      (hemisphereHeight w₂ hw₂ hu₂ H) (C p)
  exact sphereSupportMap_coordinate_change hg₁.1 hg₂.1 hg₁.2 hg₂.2 hH₂.contDiffOn
    isOpen_univ isOpen_univ (mem_univ p) (mem_univ (C p)) hC hQeq hHeq hunit₁ hunit₂

end
end TightVer401
