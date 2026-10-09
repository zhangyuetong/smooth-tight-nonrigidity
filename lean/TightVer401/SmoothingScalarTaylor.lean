import TightVer401.SmoothingCutoff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

namespace TightVer401
noncomputable section
open MeasureTheory
open scoped ContDiff

/-- Actual second-order Taylor factorization on both sides of zero. -/
theorem smoothing_scalar_taylor_second {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hzero : f 0 = 0) (hfirst : deriv f 0 = 0) (t : ℝ) :
    f t = t^2 * ∫ u in 0..1, (1 - u) * deriv (deriv f) (u * t) := by
  by_cases ht : t = 0
  · simp [ht, hzero]
  have hf' := (contDiff_infty_iff_deriv.mp hf).2
  have hf'' := (contDiff_infty_iff_deriv.mp hf').2
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun x : ℝ => t - x) (v := deriv f) (u' := fun _ => -1)
    (v' := deriv (deriv f)) (a := 0) (b := t)
    ((continuous_const.sub continuous_id).continuousOn) hf'.continuous.continuousOn
    (fun x _ => by
      have h := ((hasDerivAt_const x t).sub (hasDerivAt_id x)).congr_of_eventuallyEq
        (f₁ := fun y : ℝ => t - y) (Filter.Eventually.of_forall (fun _ => rfl))
      simpa only [zero_sub] using h)
    (fun x _ => (hf'.differentiable (by simp) x).hasDerivAt)
    (continuous_const.intervalIntegrable 0 t) (hf''.continuous.intervalIntegrable 0 t)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => (hf.differentiable (by simp) x).hasDerivAt) (hf'.continuous.intervalIntegrable 0 t)
  have he : (∫ x in 0..t, (t - x) * deriv (deriv f) x) = f t := by
    simpa only [sub_self, zero_mul, sub_zero, hfirst, mul_zero, neg_one_mul,
      intervalIntegral.integral_neg, zero_sub, neg_neg, hftc, hzero] using hi
  have hm : (∫ u in 0..1, (t - u * t) * deriv (deriv f) (u * t)) =
      t⁻¹ * ∫ x in 0..t, (t - x) * deriv (deriv f) x := by
    simpa only [zero_mul, one_mul, smul_eq_mul] using
      intervalIntegral.integral_comp_mul_right (fun x : ℝ => (t - x) * deriv (deriv f) x)
        (a := 0) (b := 1) ht
  have hc : (∫ u in 0..1, (t - u * t) * deriv (deriv f) (u * t)) =
      t * ∫ u in 0..1, (1 - u) * deriv (deriv f) (u * t) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u _
    ring
  rw [he, hc] at hm
  calc
    f t = t * (t⁻¹ * f t) := by field_simp
    _ = t * (t * ∫ u in 0..1, (1 - u) * deriv (deriv f) (u * t)) := by rw [← hm]
    _ = _ := by ring

end
end TightVer401
