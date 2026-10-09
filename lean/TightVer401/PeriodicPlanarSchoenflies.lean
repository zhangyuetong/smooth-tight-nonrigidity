import TightVer401.NativePlanarSchoenflies
import TightVer401.PeriodicComplexJordan

namespace TightVer401
noncomputable section
open Set Function Metric
open scoped ContDiff Manifold Topology
local instance periodicSchoenfliesChart (L : ℝ) [Fact (0 < L)] :
    ChartedSpace ℝ (AddCircle L) := periodCircleChartedSpace L

theorem periodicComplexCurve_exists_filling {L : ℝ} [hL : Fact (0 < L)]
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f L)
    (hi : InjOn f (Ico 0 L)) :
    ∃ H : ℂ ≃ₜ ℂ, range f = H '' sphere (0 : ℂ) 1 := by
  let e := AddCircle.homeomorphCircle (ne_of_gt hL.out)
  let g : Circle → ℂ := hp.lift ∘ e.symm
  have hg : Continuous g := (periodicLift_contMDiff hf hp).continuous.comp e.symm.continuous
  have hgi : Injective g := (periodicComplexCurve_lift_injective hp hi).comp e.symm.injective
  obtain ⟨H, hH⟩ := exists_complex_schoenflies g hg hgi
  have hrf : range g = range f := by
    ext z
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective (e.symm q)
      refine ⟨t, ?_⟩
      change f t = hp.lift (e.symm q)
      rw [← ht, hp.lift_coe]
    · rintro ⟨t, rfl⟩
      refine ⟨e (periodProjection L t), ?_⟩
      simp only [g, comp_apply, e.symm_apply_apply]
      exact periodicLift_coe hp t
  refine ⟨H, hrf.symm.trans ?_⟩
  ext z
  constructor
  · rintro ⟨q, rfl⟩
    refine ⟨(q : ℂ), ?_, hH q⟩
    simp only [mem_sphere, dist_zero_right, Circle.norm_coe]
  · rintro ⟨w, hw, rfl⟩
    have hn : ‖w‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hw
    let q : Circle := ⟨w, by simpa [Submonoid.unitSphere] using hn⟩
    exact ⟨q, (hH q).symm⟩
end
end TightVer401
