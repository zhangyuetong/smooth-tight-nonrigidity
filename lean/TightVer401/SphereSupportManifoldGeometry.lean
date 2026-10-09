import TightVer401.SphereSupportOpenGeometry

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology RealInnerProductSpace Manifold
set_option backward.isDefEq.respectTransparency false

local instance : Fact (Module.finrank ℝ Ambient = 2 + 1) := ⟨by simp [Ambient]⟩

theorem sphereHemisphereChart_mdifferentiable (w : Ambient) (hw : w ≠ 0) (hu : ‖w‖ = 1) :
    (sphereHemisphereChart w hw hu).MDifferentiable 𝓘(ℝ, Coord) (𝓡 2) := by
  constructor
  · exact (sphereHemispherePoint_contMDiff w hw hu).contMDiffOn.mdifferentiableOn (by simp)
  · intro q hq
    exact ((sphereHemisphereInverse_contDiffAt w hw hq).contMDiffAt.comp q
      (contMDiff_coe_sphere q)).mdifferentiableAt (by simp) |>.mdifferentiableWithinAt

theorem globalSphereSupport_manifold_geometryOn {H : RoundSphere → ℝ} {Ω : Set RoundSphere}
    (hH : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H Ω) (hΩ : IsOpen Ω)
    (w : Ambient) (hw : w ≠ 0) (hu : ‖w‖ = 1) {p : Coord}
    (hp : p ∈ hemisphereDomain w hw hu Ω)
    (hdet : (sphereSupportTensor (inducedMetric (sphereHemisphere w hw))
      (hemisphereHeight w hw hu H) p).det ≠ 0) :
    Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, Ambient) (globalSphereSupport H)
      (sphereHemispherePoint w hw hu p)) ∧
    (∀ v : TangentSpace (𝓡 2) (sphereHemispherePoint w hw hu p),
      @inner ℝ Ambient _ (mfderiv (𝓡 2) 𝓘(ℝ, Ambient) (globalSphereSupport H)
        (sphereHemispherePoint w hw hu p) v) (sphereHemisphere w hw p) = 0) := by
  have hg := globalSphereSupport_chart_geometryOn hH hΩ w hw hu p hp
  have hA := (globalSphereSupport_contMDiffOn hH hΩ).contMDiffAt (hΩ.mem_nhds hp)
  have hP := (sphereHemispherePoint_contMDiff w hw hu).contMDiffAt (x := p)
  have hd := mfderiv_comp p (hA.mdifferentiableAt (by simp)) (hP.mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at hd
  change fderiv ℝ (fun z => globalSphereSupport H (sphereHemispherePoint w hw hu z)) p = _ at hd
  have hs := (sphereHemisphereChart_mdifferentiable w hw hu).mfderiv_surjective
    (x := p) (mem_univ p)
  change Function.Surjective (mfderiv 𝓘(ℝ, Coord) (𝓡 2) (sphereHemispherePoint w hw hu) p) at hs
  have hi := (hg.2.2.2.2 hdet).1
  constructor
  · intro v z hvz
    obtain ⟨a, ha⟩ := hs v
    obtain ⟨b, hb⟩ := hs z
    have hab : a = b := hi (by
      rw [hd]
      change (mfderiv (𝓡 2) 𝓘(ℝ, Ambient) (globalSphereSupport H)
        (sphereHemispherePoint w hw hu p))
        ((mfderiv 𝓘(ℝ, Coord) (𝓡 2) (sphereHemispherePoint w hw hu) p) a) =
        (mfderiv (𝓡 2) 𝓘(ℝ, Ambient) (globalSphereSupport H)
          (sphereHemispherePoint w hw hu p))
          ((mfderiv 𝓘(ℝ, Coord) (𝓡 2) (sphereHemispherePoint w hw hu) p) b)
      rwa [ha, hb])
    rw [← ha, ← hb, hab]
  · intro v
    obtain ⟨a, ha⟩ := hs v
    have hn := hg.2.1.2 a
    rw [hd] at hn
    rw [← ha]
    exact hn

end
end TightVer401
