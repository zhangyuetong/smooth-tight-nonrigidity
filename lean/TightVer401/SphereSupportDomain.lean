import TightVer401.SphereSupportGlobal

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology RealInnerProductSpace Manifold

local instance : Fact (Module.finrank ℝ Ambient = 2 + 1) := ⟨by simp [Ambient]⟩

def hemisphereDomain (w : Ambient) (hw : w ≠ 0) (hu : ‖w‖ = 1)
    (Ω : Set RoundSphere) : Set Coord := sphereHemispherePoint w hw hu ⁻¹' Ω

theorem hemisphereDomain_isOpen (w : Ambient) (hw : w ≠ 0) (hu : ‖w‖ = 1)
    {Ω : Set RoundSphere} (hΩ : IsOpen Ω) : IsOpen (hemisphereDomain w hw hu Ω) :=
  hΩ.preimage (sphereHemispherePoint_contMDiff w hw hu).continuous

theorem hemisphereHeight_contDiffOn {H : RoundSphere → ℝ} {Ω : Set RoundSphere}
    (hH : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H Ω)
    (w : Ambient) (hw : w ≠ 0) (hu : ‖w‖ = 1) :
    ContDiffOn ℝ ∞ (hemisphereHeight w hw hu H) (hemisphereDomain w hw hu Ω) :=
  (hH.comp (sphereHemispherePoint_contMDiff w hw hu).contMDiffOn (fun _ h => h)).contDiffOn

theorem hemisphereSupport_contDiffOn {H : RoundSphere → ℝ} {Ω : Set RoundSphere}
    (hH : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H Ω) (hΩ : IsOpen Ω)
    (w : Ambient) (hw : w ≠ 0) (hu : ‖w‖ = 1) :
    ContDiffOn ℝ ∞ (hemisphereSupport w hw hu H) (hemisphereDomain w hw hu Ω) := by
  have hg := sphereHemisphere_metric w hw hu
  let V := hemisphereDomain w hw hu Ω
  have hgV : SmoothPositiveOn (inducedMetric (sphereHemisphere w hw)) V :=
    ⟨fun i j => (hg.1.1 i j).mono (subset_univ _), fun p _ => hg.1.2 p (mem_univ p)⟩
  exact sphereSupportMap_contDiffOn hgV (sphereHemisphere_contDiff w hw hu).contDiffOn
    (hemisphereHeight_contDiffOn hH w hw hu) (hemisphereDomain_isOpen w hw hu hΩ)

theorem hemisphereSupport_agrees_domain (w₁ w₂ : Ambient) (hw₁ : w₁ ≠ 0) (hw₂ : w₂ ≠ 0)
    (hu₁ : ‖w₁‖ = 1) (hu₂ : ‖w₂‖ = 1) (H : RoundSphere → ℝ)
    {V₂ : Set Coord} (hV₂ : IsOpen V₂)
    (hH₂ : ContDiffOn ℝ ∞ (hemisphereHeight w₂ hw₂ hu₂ H) V₂)
    {p : Coord} (hp : 0 < inner ℝ w₂ (sphereHemisphere w₁ hw₁ p))
    (hCp : sphereHemisphereInverse w₂ hw₂ (sphereHemisphere w₁ hw₁ p) ∈ V₂) :
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
    change H (sphereHemispherePoint w₁ hw₁ hu₁ q) = H (sphereHemispherePoint w₂ hw₂ hu₂ (C q))
    exact congrArg H (Subtype.ext hq)
  have hg₁ := sphereHemisphere_metric w₁ hw₁ hu₁
  have hg₂ := sphereHemisphere_metric w₂ hw₂ hu₂
  have hgV : SmoothPositiveOn (inducedMetric (sphereHemisphere w₂ hw₂)) V₂ :=
    ⟨fun i j => (hg₂.1.1 i j).mono (subset_univ _), fun q _ => hg₂.1.2 q (mem_univ q)⟩
  have hQV : IsometricOn (inducedMetric (sphereHemisphere w₂ hw₂)) (sphereHemisphere w₂ hw₂) V₂ :=
    ⟨hg₂.2.1.mono (subset_univ _), fun q _ => hg₂.2.2 q (mem_univ q)⟩
  have hC : DifferentiableAt ℝ C p :=
    ((sphereHemisphereInverse_contDiffAt w₂ hw₂ hp).comp p
      (sphereHemisphere_contDiff w₁ hw₁ hu₁).contDiffAt).differentiableAt (by simp)
  have huQ₁ : ∀ q ∈ univ, inner ℝ (sphereHemisphere w₁ hw₁ q) (sphereHemisphere w₁ hw₁ q) = 1 := by
    intro q _
    rw [real_inner_self_eq_norm_sq, sphereHemisphere_norm w₁ hw₁ hu₁, one_pow]
  have huQ₂ : ∀ q ∈ V₂, inner ℝ (sphereHemisphere w₂ hw₂ q) (sphereHemisphere w₂ hw₂ q) = 1 := by
    intro q _
    rw [real_inner_self_eq_norm_sq, sphereHemisphere_norm w₂ hw₂ hu₂, one_pow]
  change sphereSupportMap (inducedMetric (sphereHemisphere w₁ hw₁)) (sphereHemisphere w₁ hw₁)
    (hemisphereHeight w₁ hw₁ hu₁ H) p =
    sphereSupportMap (inducedMetric (sphereHemisphere w₂ hw₂)) (sphereHemisphere w₂ hw₂)
      (hemisphereHeight w₂ hw₂ hu₂ H) (C p)
  exact sphereSupportMap_coordinate_change hg₁.1 hgV hg₁.2 hQV hH₂ isOpen_univ hV₂
    (mem_univ p) hCp hC hQeq hHeq huQ₁ huQ₂

end
end TightVer401
