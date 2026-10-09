import TightVer401.SphereSupportDomain

/-! Support reconstruction on an arbitrary open subset of the actual sphere.
The height need only be smooth on that subset. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology RealInnerProductSpace Manifold

local instance : Fact (Module.finrank ℝ Ambient = 2 + 1) := ⟨by simp [Ambient]⟩

theorem globalSphereSupport_chartOn {H : RoundSphere → ℝ} {Ω : Set RoundSphere}
    (hH : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H Ω) (hΩ : IsOpen Ω)
    (w : Ambient) (hw : w ≠ 0) (hu : ‖w‖ = 1) {p : Coord}
    (hp : p ∈ hemisphereDomain w hw hu Ω) :
    globalSphereSupport H (sphereHemispherePoint w hw hu p) = hemisphereSupport w hw hu H p := by
  let q := sphereHemispherePoint w hw hu p
  have hq : q ∈ Ω := hp
  have hpos : 0 < inner ℝ q.val (sphereHemisphere w hw p) := by
    change 0 < inner ℝ q.val q.val
    rw [real_inner_self_eq_norm_sq, roundSphere_norm, one_pow]
    exact zero_lt_one
  have hi : sphereHemisphereInverse q.val (roundSphere_ne_zero q) (sphereHemisphere w hw p) = 0 := by
    change sphereHemisphereInverse q.val (roundSphere_ne_zero q) q.val = 0
    calc
      sphereHemisphereInverse q.val (roundSphere_ne_zero q) q.val =
        sphereHemisphereInverse q.val (roundSphere_ne_zero q)
          (sphereHemisphere q.val (roundSphere_ne_zero q) 0) :=
        congrArg _ (sphereHemisphere_zero q.val (roundSphere_ne_zero q) (roundSphere_norm q)).symm
      _ = 0 := sphereHemisphere_left_inverse _ _ (roundSphere_norm q) 0
  have hpoint : sphereHemispherePoint q.val (roundSphere_ne_zero q) (roundSphere_norm q) 0 = q := by
    apply Subtype.ext
    exact sphereHemisphere_zero _ _ (roundSphere_norm q)
  have hzero : (0 : Coord) ∈ hemisphereDomain q.val (roundSphere_ne_zero q) (roundSphere_norm q) Ω := by
    change sphereHemispherePoint q.val (roundSphere_ne_zero q) (roundSphere_norm q) 0 ∈ Ω
    rwa [hpoint]
  have he := hemisphereSupport_agrees_domain w q.val hw (roundSphere_ne_zero q) hu
    (roundSphere_norm q) H (hemisphereDomain_isOpen _ _ _ hΩ)
    (hemisphereHeight_contDiffOn hH _ _ _) hpos (by rwa [hi])
  rw [hi] at he
  exact he.symm

theorem globalSphereSupport_on_hemisphereOn {H : RoundSphere → ℝ} {Ω : Set RoundSphere}
    (hH : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H Ω) (hΩ : IsOpen Ω)
    (w : Ambient) (hw : w ≠ 0) (hu : ‖w‖ = 1) {q : RoundSphere}
    (hqΩ : q ∈ Ω) (hq : 0 < inner ℝ w q.val) :
    globalSphereSupport H q = hemisphereSupport w hw hu H (sphereHemisphereInverse w hw q.val) := by
  have he : sphereHemispherePoint w hw hu (sphereHemisphereInverse w hw q.val) = q := by
    apply Subtype.ext
    exact sphereHemisphere_right_inverse w hw hu (roundSphere_norm q) hq
  calc
    globalSphereSupport H q = globalSphereSupport H
      (sphereHemispherePoint w hw hu (sphereHemisphereInverse w hw q.val)) := congrArg _ he.symm
    _ = _ := globalSphereSupport_chartOn hH hΩ w hw hu (by change _ ∈ Ω; rwa [he])

theorem globalSphereSupport_contMDiffOn {H : RoundSphere → ℝ} {Ω : Set RoundSphere}
    (hH : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H Ω) (hΩ : IsOpen Ω) :
    ContMDiffOn (𝓡 2) 𝓘(ℝ, Ambient) ∞ (globalSphereSupport H) Ω := by
  intro q hqΩ
  have hpos : 0 < inner ℝ q.val q.val := by
    rw [real_inner_self_eq_norm_sq, roundSphere_norm, one_pow]
    exact zero_lt_one
  have hpoint : sphereHemispherePoint q.val (roundSphere_ne_zero q) (roundSphere_norm q) 0 = q := by
    apply Subtype.ext
    exact sphereHemisphere_zero _ _ (roundSphere_norm q)
  have hzero : (0 : Coord) ∈ hemisphereDomain q.val (roundSphere_ne_zero q) (roundSphere_norm q) Ω := by
    change sphereHemispherePoint q.val (roundSphere_ne_zero q) (roundSphere_norm q) 0 ∈ Ω
    rwa [hpoint]
  have hi0 : sphereHemisphereInverse q.val (roundSphere_ne_zero q) q.val = 0 := by
    calc
      sphereHemisphereInverse q.val (roundSphere_ne_zero q) q.val =
        sphereHemisphereInverse q.val (roundSphere_ne_zero q)
          (sphereHemisphere q.val (roundSphere_ne_zero q) 0) :=
        congrArg _ (sphereHemisphere_zero q.val (roundSphere_ne_zero q) (roundSphere_norm q)).symm
      _ = 0 := sphereHemisphere_left_inverse _ _ (roundSphere_norm q) 0
  have hi : ContMDiffAt (𝓡 2) 𝓘(ℝ, Coord) ∞
      (fun x : RoundSphere => sphereHemisphereInverse q.val (roundSphere_ne_zero q) x.val) q :=
    (sphereHemisphereInverse_contDiffAt q.val (roundSphere_ne_zero q) hpos).contMDiffAt.comp q
      (contMDiff_coe_sphere q)
  have hs := (hemisphereSupport_contDiffOn hH hΩ q.val (roundSphere_ne_zero q)
    (roundSphere_norm q)).contDiffAt ((hemisphereDomain_isOpen _ _ _ hΩ).mem_nhds hzero)
  have hs' : ContDiffAt ℝ ∞ (hemisphereSupport q.val (roundSphere_ne_zero q) (roundSphere_norm q) H)
      (sphereHemisphereInverse q.val (roundSphere_ne_zero q) q.val) := by rwa [hi0]
  have ha := hs'.contMDiffAt.comp q hi
  have hopen : IsOpen {x : RoundSphere | 0 < inner ℝ q.val x.val} :=
    isOpen_lt continuous_const (continuous_const.inner continuous_subtype_val)
  have heq : globalSphereSupport H =ᶠ[𝓝 q]
      (fun x : RoundSphere => hemisphereSupport q.val (roundSphere_ne_zero q) (roundSphere_norm q) H
        (sphereHemisphereInverse q.val (roundSphere_ne_zero q) x.val)) := by
    filter_upwards [hΩ.mem_nhds hqΩ, hopen.mem_nhds hpos] with x hxΩ hx
    exact globalSphereSupport_on_hemisphereOn hH hΩ q.val (roundSphere_ne_zero q) (roundSphere_norm q) hxΩ hx
  exact (ha.congr_of_eventuallyEq heq).contMDiffWithinAt

end
end TightVer401
