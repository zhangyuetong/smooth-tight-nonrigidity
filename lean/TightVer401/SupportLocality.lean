import TightVer401.SphereSupportOpen

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology RealInnerProductSpace Manifold

local instance : Fact (Module.finrank ℝ Ambient = 2 + 1) := ⟨by simp [Ambient]⟩

theorem sphereSupportMap_congr_of_eventuallyEq {g : MetricField} {Q : Coord → Ambient}
    {H K : Coord → ℝ} {p : Coord} (he : H =ᶠ[𝓝 p] K) :
    sphereSupportMap g Q H p = sphereSupportMap g Q K p := by
  unfold sphereSupportMap sphereGradient coordPartial
  rw [he.fderiv_eq, he.eq_of_nhds]

theorem globalSphereSupport_congr_of_eventuallyEq {H K : RoundSphere → ℝ}
    {q : RoundSphere} (he : H =ᶠ[𝓝 q] K) :
    globalSphereSupport H q = globalSphereSupport K q := by
  let P := sphereHemispherePoint q.val (roundSphere_ne_zero q) (roundSphere_norm q)
  have hP : P 0 = q := by
    apply Subtype.ext
    exact sphereHemisphere_zero _ _ (roundSphere_norm q)
  have ht : Tendsto P (𝓝 0) (𝓝 q) := by
    rw [← hP]
    exact (sphereHemispherePoint_contMDiff _ _ _).continuous.tendsto 0
  have hh : hemisphereHeight q.val (roundSphere_ne_zero q) (roundSphere_norm q) H =ᶠ[𝓝 0]
      hemisphereHeight q.val (roundSphere_ne_zero q) (roundSphere_norm q) K :=
    he.comp_tendsto ht
  exact sphereSupportMap_congr_of_eventuallyEq hh

theorem globalSphereSupport_congr_on_open {H K : RoundSphere → ℝ} {Ω : Set RoundSphere}
    (hΩ : IsOpen Ω) (he : EqOn H K Ω) {q : RoundSphere} (hq : q ∈ Ω) :
    globalSphereSupport H q = globalSphereSupport K q := by
  apply globalSphereSupport_congr_of_eventuallyEq
  filter_upwards [hΩ.mem_nhds hq] with x hx
  exact he hx

end
end TightVer401
