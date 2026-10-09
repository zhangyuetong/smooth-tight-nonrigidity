import TightVer401.SphereSupportAtlas

/-! A global support map on the actual two-sphere, defined using centered
OpenAI hemisphere charts. Agreement of gradients makes this choice smooth. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology RealInnerProductSpace Manifold
set_option backward.isDefEq.respectTransparency false

local instance : Fact (Module.finrank ℝ Ambient = 2 + 1) := ⟨by simp [Ambient]⟩

theorem hemisphereHeight_contDiff {H : RoundSphere → ℝ}
    (hH : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ H)
    (w : Ambient) (hw : w ≠ 0) (hu : ‖w‖ = 1) :
    ContDiff ℝ ∞ (hemisphereHeight w hw hu H) :=
  (hH.comp (sphereHemispherePoint_contMDiff w hw hu)).contDiff

theorem hemisphereSupport_contDiff {H : RoundSphere → ℝ}
    (hH : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ H)
    (w : Ambient) (hw : w ≠ 0) (hu : ‖w‖ = 1) :
    ContDiff ℝ ∞ (hemisphereSupport w hw hu H) := by
  have hg := sphereHemisphere_metric w hw hu
  apply contDiffOn_univ.mp
  exact sphereSupportMap_contDiffOn hg.1 (sphereHemisphere_contDiff w hw hu).contDiffOn
    (hemisphereHeight_contDiff hH w hw hu).contDiffOn isOpen_univ

def globalSphereSupport (H : RoundSphere → ℝ) : RoundSphere → Ambient :=
  fun q => hemisphereSupport q.val (roundSphere_ne_zero q) (roundSphere_norm q) H 0

theorem globalSphereSupport_chart {H : RoundSphere → ℝ}
    (hH : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ H)
    (w : Ambient) (hw : w ≠ 0) (hu : ‖w‖ = 1) (p : Coord) :
    globalSphereSupport H (sphereHemispherePoint w hw hu p) = hemisphereSupport w hw hu H p := by
  let q := sphereHemispherePoint w hw hu p
  have hpos : 0 < inner ℝ q.val (sphereHemisphere w hw p) := by
    change 0 < inner ℝ q.val q.val
    rw [real_inner_self_eq_norm_sq, roundSphere_norm, one_pow]
    exact zero_lt_one
  have he := hemisphereSupport_agrees w q.val hw (roundSphere_ne_zero q) hu
    (roundSphere_norm q) H (hemisphereHeight_contDiff hH _ _ _) hpos
  have hi : sphereHemisphereInverse q.val (roundSphere_ne_zero q) (sphereHemisphere w hw p) = 0 := by
    change sphereHemisphereInverse q.val (roundSphere_ne_zero q) q.val = 0
    calc
      sphereHemisphereInverse q.val (roundSphere_ne_zero q) q.val =
        sphereHemisphereInverse q.val (roundSphere_ne_zero q)
          (sphereHemisphere q.val (roundSphere_ne_zero q) 0) :=
        congrArg _ (sphereHemisphere_zero q.val (roundSphere_ne_zero q) (roundSphere_norm q)).symm
      _ = 0 := sphereHemisphere_left_inverse _ _ (roundSphere_norm q) 0
  rw [hi] at he
  exact he.symm

theorem globalSphereSupport_on_hemisphere {H : RoundSphere → ℝ}
    (hH : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ H)
    (w : Ambient) (hw : w ≠ 0) (hu : ‖w‖ = 1) {q : RoundSphere}
    (hq : 0 < inner ℝ w q.val) :
    globalSphereSupport H q = hemisphereSupport w hw hu H (sphereHemisphereInverse w hw q.val) := by
  have he : sphereHemispherePoint w hw hu (sphereHemisphereInverse w hw q.val) = q := by
    apply Subtype.ext
    exact sphereHemisphere_right_inverse w hw hu (roundSphere_norm q) hq
  calc
    globalSphereSupport H q = globalSphereSupport H
      (sphereHemispherePoint w hw hu (sphereHemisphereInverse w hw q.val)) := congrArg _ he.symm
    _ = _ := globalSphereSupport_chart hH w hw hu _

theorem globalSphereSupport_contMDiff {H : RoundSphere → ℝ}
    (hH : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ H) :
    ContMDiff (𝓡 2) 𝓘(ℝ, Ambient) ∞ (globalSphereSupport H) := by
  intro q
  have hpos : 0 < inner ℝ q.val q.val := by
    rw [real_inner_self_eq_norm_sq, roundSphere_norm, one_pow]
    exact zero_lt_one
  have hi : ContMDiffAt (𝓡 2) 𝓘(ℝ, Coord) ∞
      (fun x : RoundSphere => sphereHemisphereInverse q.val (roundSphere_ne_zero q) x.val) q :=
    (sphereHemisphereInverse_contDiffAt q.val (roundSphere_ne_zero q) hpos).contMDiffAt.comp q
      (contMDiff_coe_sphere q)
  have ha := (hemisphereSupport_contDiff hH q.val (roundSphere_ne_zero q)
    (roundSphere_norm q)).contMDiff.contMDiffAt.comp q hi
  apply ha.congr_of_eventuallyEq
  have hopen : IsOpen {x : RoundSphere | 0 < inner ℝ q.val x.val} :=
    isOpen_lt continuous_const (continuous_const.inner continuous_subtype_val)
  filter_upwards [hopen.mem_nhds hpos] with x hx
  exact globalSphereSupport_on_hemisphere hH q.val (roundSphere_ne_zero q) (roundSphere_norm q) hx

theorem globalSphereSupport_height {H : RoundSphere → ℝ}
    (hH : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ H) (q : RoundSphere) :
    inner ℝ (globalSphereSupport H q) q.val = H q := by
  let Q := sphereHemisphere q.val (roundSphere_ne_zero q)
  let P := sphereHemispherePoint q.val (roundSphere_ne_zero q) (roundSphere_norm q)
  have hP : P 0 = q := by
    apply Subtype.ext
    exact sphereHemisphere_zero _ _ (roundSphere_norm q)
  have hQ : Q 0 = q.val := sphereHemisphere_zero _ _ (roundSphere_norm q)
  have hunit : ∀ p ∈ univ, inner ℝ (Q p) (Q p) = 1 := by
    intro p _
    rw [real_inner_self_eq_norm_sq, sphereHemisphere_norm _ _ (roundSphere_norm q), one_pow]
  have hh := sphereSupportMap_height (sphereHemisphere_contDiff _ _ (roundSphere_norm q)).contDiffOn
    isOpen_univ (mem_univ (0 : Coord)) hunit
      (g := inducedMetric Q) (H := hemisphereHeight q.val (roundSphere_ne_zero q) (roundSphere_norm q) H)
  change inner ℝ (globalSphereSupport H q) (Q 0) = H (P 0) at hh
  rwa [hQ, hP] at hh

end
end TightVer401
