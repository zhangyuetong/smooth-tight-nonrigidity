import TightVer401.NormalLoopBalance
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace TightVer401
noncomputable section
open Set MeasureTheory

def momentNonlinearPeriod (a g : ℝ → ℝ) (L : ℝ) : ℝ :=
  ∫ r in 0..L, g r / Real.sqrt (a r)

theorem momentNonlinearPeriod_intervalIntegrable {a g : ℝ → ℝ}
    (ha : Continuous a) (hg : Continuous g) (hpos : ∀ r, 0 < a r) (L : ℝ) :
    IntervalIntegrable (fun r => g r / Real.sqrt (a r)) volume 0 L :=
  (hg.div (Real.continuous_sqrt.comp ha)
    (fun r => ne_of_gt (Real.sqrt_pos.mpr (hpos r)))).intervalIntegrable 0 L

theorem momentNonlinearPeriod_continuous {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] [LocallyCompactSpace X]
    {a : X → ℝ → ℝ} {g : ℝ → ℝ} (ha : Continuous a.uncurry)
    (hg : Continuous g) (hpos : ∀ x r, 0 < a x r) {L : ℝ} (hL : 0 ≤ L) :
    Continuous (fun x => momentNonlinearPeriod (a x) g L) := by
  have hf : Continuous (Function.uncurry (fun x r => g r / Real.sqrt (a x r))) :=
    (hg.comp continuous_snd).div (Real.continuous_sqrt.comp ha)
      (fun p => ne_of_gt (Real.sqrt_pos.mpr (hpos p.1 p.2)))
  have hc : Continuous (fun x => ∫ r in Icc 0 L, g r / Real.sqrt (a x r)) :=
    continuous_parametric_integral_of_continuous hf isCompact_Icc
  have he : (fun x => momentNonlinearPeriod (a x) g L) =
      (fun x => ∫ r in Icc 0 L, g r / Real.sqrt (a x r)) := by
    funext x
    unfold momentNonlinearPeriod
    rw [intervalIntegral.integral_of_le hL, integral_Icc_eq_integral_Ioc]
  rwa [he]

theorem momentNonlinearPeriod_slowdown {b g : ℝ → ℝ} {t L : ℝ}
    (hpos : ∀ r, 0 < b r) (ht : t < 1) :
    momentNonlinearPeriod (fun r => (1 - t) * b r) g L =
      (Real.sqrt (1 - t))⁻¹ * momentNonlinearPeriod b g L := by
  have he : (fun r => g r / Real.sqrt ((1 - t) * b r)) =
      (fun r => (Real.sqrt (1 - t))⁻¹ * (g r / Real.sqrt (b r))) := by
    funext r
    rw [Real.sqrt_mul (by linarith : 0 ≤ 1 - t)]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  unfold momentNonlinearPeriod
  rw [he, intervalIntegral.integral_const_mul]

end
end TightVer401
