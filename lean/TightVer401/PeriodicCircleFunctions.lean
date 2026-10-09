import TightVer401.PeriodCircle

namespace TightVer401
noncomputable section
open scoped Manifold ContDiff

theorem periodicLift_contMDiff {L : ℝ} [Fact (0 < L)] {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {f : ℝ → V}
    (hf : ContDiff ℝ ∞ f) (hperiod : Function.Periodic f L) :
    letI := periodCircleChartedSpace L
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, V) ∞ hperiod.lift := by
  apply periodCircle_descend_smooth L hperiod.lift
  convert! hf using 1

theorem periodicLift_coe {L : ℝ} {V : Type*} {f : ℝ → V}
    (hperiod : Function.Periodic f L) (s : ℝ) :
    hperiod.lift (periodProjection L s) = f s := hperiod.lift_coe s

theorem periodicLift_unique {L : ℝ} {V : Type*} {f : ℝ → V}
    (hperiod : Function.Periodic f L) (g : AddCircle L → V)
    (hg : ∀ s, g (periodProjection L s) = f s) : g = hperiod.lift := by
  funext x
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective x
  exact (hg s).trans (hperiod.lift_coe s).symm

end
end TightVer401
