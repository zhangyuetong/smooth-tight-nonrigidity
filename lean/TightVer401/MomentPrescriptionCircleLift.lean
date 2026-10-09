import TightVer401.MomentPrescriptionPath
import TightVer401.PeriodicCircleFunctions

namespace TightVer401
noncomputable section
open Set MeasureTheory
open scoped ContDiff Manifold
set_option backward.isDefEq.respectTransparency false

theorem momentPrescription_lift_to_circle {m : ℕ} (L : ℝ) [Fact (0 < L)]
    {a : ℝ → ℝ} (b g : AddCircle L → ℝ) (f : AddCircle L → EuclideanSpace ℝ (Fin m))
    {η B : ℝ} (ha : ContDiff ℝ ∞ a) (hperiod : Function.Periodic a L)
    (hpos : ∀ r, 0 < a r)
    (hsmall : (∫ r in 0..L, ‖a r - b (periodProjection L r)‖) < η)
    (hmoment : (∫ r in 0..L, a r • f (periodProjection L r)) =
      ∫ r in 0..L, b (periodProjection L r) • f (periodProjection L r))
    (hB : momentNonlinearPeriod a (g ∘ periodProjection L) L = B) :
    letI := periodCircleChartedSpace L
    ∃ A : AddCircle L → ℝ, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ A ∧
      (∀ r, A (periodProjection L r) = a r) ∧ (∀ q, 0 < A q) ∧
      (∫ r in 0..L, ‖A (periodProjection L r) - b (periodProjection L r)‖) < η ∧
      (∫ r in 0..L, A (periodProjection L r) • f (periodProjection L r)) =
        (∫ r in 0..L, b (periodProjection L r) • f (periodProjection L r)) ∧
      (∫ r in 0..L, g (periodProjection L r) / Real.sqrt (A (periodProjection L r))) = B := by
  letI := periodCircleChartedSpace L
  let A := hperiod.lift
  have hA (r) : A (periodProjection L r) = a r := hperiod.lift_coe r
  refine ⟨A, periodicLift_contMDiff ha hperiod, hA, ?_, ?_, ?_, ?_⟩
  · intro q
    obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective q
    change 0 < A (periodProjection L r)
    rw [hA]
    exact hpos r
  · simpa only [hA] using hsmall
  · simpa only [hA] using hmoment
  · simpa only [momentNonlinearPeriod, Function.comp_apply, hA] using hB

end
end TightVer401
