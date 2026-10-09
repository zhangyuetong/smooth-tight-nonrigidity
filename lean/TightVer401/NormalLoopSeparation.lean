import TightVer401.NormalLoopNonconstant
import TightVer401.PeriodCircle

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry Set MeasureTheory
open scoped ContDiff

theorem positive_weighted_zero_of_periodic_nonneg {a f : ℝ → ℝ} {L : ℝ}
    (ha : Continuous a) (hf : Continuous f) (hL : 0 < L)
    (hpos : ∀ r, 0 < a r) (hnonneg : ∀ r, 0 ≤ f r)
    (hperiod : Function.Periodic f L) (hzero : (∫ r in 0..L, a r * f r) = 0) :
    ∀ r, f r = 0 := by
  have hI (r : ℝ) (hr : r ∈ Icc 0 L) : f r = 0 := by
    by_contra hne
    have hp : 0 < f r := (hnonneg r).lt_of_ne' hne
    have hlt := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      hL continuous_const.continuousOn (ha.mul hf).continuousOn
      (fun s _ => mul_nonneg (hpos s).le (hnonneg s)) ⟨r, hr, mul_pos (hpos r) hp⟩
    simpa only [Pi.mul_apply, intervalIntegral.integral_zero, hzero, lt_self_iff_false] using hlt
  intro r
  let k : ℤ := ⌊r / L⌋
  have hr : r - (k : ℝ) * L ∈ Icc 0 L := by
    have hk₁ := Int.floor_le (r / L)
    have hk₂ := Int.lt_floor_add_one (r / L)
    have hl₁ := (le_div_iff₀ hL).mp hk₁
    have hl₂ := (div_lt_iff₀ hL).mp hk₂
    dsimp [k]
    constructor <;> nlinarith
  rw [← hperiod.sub_int_mul_eq k]
  exact hI _ hr

theorem normalLoop_closure_halfspace_eq_zero {ζ : ℝ → Ambient} {a : ℝ → ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (ha : Continuous a) (hpos : ∀ r, 0 < a r)
    {L : ℝ} (hL : 0 < L) (hζL : Function.Periodic ζ L)
    (hmoment : normalLoopMoment a ζ (deriv ζ) L = 0) {v : Ambient}
    (hv : ∀ r, 0 ≤ inner ℝ v (normalLoopTangent ζ r)) :
    ∀ r, inner ℝ v (normalLoopTangent ζ r) = 0 := by
  have hP := (normalLoop_actual_smooth hζ).1.continuous
  have hI : IntervalIntegrable (fun r => a r • normalLoopTangent ζ r) volume 0 L :=
    (ha.smul hP).intervalIntegrable 0 L
  have hint := (innerSL ℝ v).intervalIntegral_comp_comm hI
  change (∫ r in 0..L, inner ℝ v (a r • normalLoopTangent ζ r)) =
    inner ℝ v (normalLoopMoment a ζ (deriv ζ) L) at hint
  rw [hmoment, inner_zero_right] at hint
  have hp : Function.Periodic (fun r => inner ℝ v (normalLoopTangent ζ r)) L :=
    fun r => congrArg (fun x => inner ℝ v x) ((normalLoop_actual_periodic hζ hζL).1 r)
  apply positive_weighted_zero_of_periodic_nonneg ha (continuous_const.inner hP) hL hpos hv hp
  simpa only [real_inner_smul_right] using hint

end
end TightVer401
