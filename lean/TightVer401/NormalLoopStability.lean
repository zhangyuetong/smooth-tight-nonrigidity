import TightVer401.NormalLoopActual

namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff

theorem normalLoopTangent_norm {ζ : ℝ → Ambient} (hζ : ContDiff ℝ ∞ ζ)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1) (r : ℝ) :
    ‖normalLoopTangent ζ r‖ = 1 := by
  have h := ((normalLoop_actual_frame hζ hunit hspeed r).1).1
  rw [real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (normalLoopTangent ζ r)]

theorem normalLoopCurve_sub {a b : ℝ → ℝ} {ζ : ℝ → Ambient}
    (ha : Continuous a) (hb : Continuous b) (hζ : ContDiff ℝ ∞ ζ) (r : ℝ) :
    normalLoopCurve a ζ (deriv ζ) r - normalLoopCurve b ζ (deriv ζ) r =
      ∫ t in 0..r, (a t - b t) • normalLoopTangent ζ t := by
  have hP := (normalLoop_actual_smooth hζ).1.continuous
  dsimp only [normalLoopCurve, rawPrimitive]
  change (∫ t in 0..r, a t • normalLoopTangent ζ t) -
    (∫ t in 0..r, b t • normalLoopTangent ζ t) = _
  have hs : (∫ t in 0..r, a t • normalLoopTangent ζ t - b t • normalLoopTangent ζ t) =
      (∫ t in 0..r, a t • normalLoopTangent ζ t) -
        (∫ t in 0..r, b t • normalLoopTangent ζ t) := by
    simpa only [Pi.sub_apply, Pi.smul_apply'] using
      intervalIntegral.integral_sub ((ha.smul hP).intervalIntegrable 0 r)
        ((hb.smul hP).intervalIntegrable 0 r)
  rw [← hs]
  apply intervalIntegral.integral_congr
  intro t _
  exact (sub_smul (a t) (b t) (normalLoopTangent ζ t)).symm

theorem normalLoopCurve_norm_sub_le {a b : ℝ → ℝ} {ζ : ℝ → Ambient}
    (ha : Continuous a) (hb : Continuous b) (hζ : ContDiff ℝ ∞ ζ)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1)
    {r : ℝ} (hr : 0 ≤ r) :
    ‖normalLoopCurve a ζ (deriv ζ) r - normalLoopCurve b ζ (deriv ζ) r‖ ≤
      ∫ t in 0..r, |a t - b t| := by
  rw [normalLoopCurve_sub ha hb hζ]
  have he : (fun t => ‖(a t - b t) • normalLoopTangent ζ t‖) =
      (fun t => |a t - b t|) := by
    funext t
    rw [norm_smul, normalLoopTangent_norm hζ hunit hspeed, mul_one, Real.norm_eq_abs]
  exact (intervalIntegral.norm_integral_le_integral_norm hr).trans_eq (congrArg (fun f : ℝ → ℝ => ∫ t in 0..r, f t) he)

theorem normalLoopCurve_uniform_norm_sub_le {a b : ℝ → ℝ} {ζ : ℝ → Ambient}
    (ha : Continuous a) (hb : Continuous b) (hζ : ContDiff ℝ ∞ ζ)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1)
    {L r : ℝ} (hr : r ∈ Icc 0 L) :
    ‖normalLoopCurve a ζ (deriv ζ) r - normalLoopCurve b ζ (deriv ζ) r‖ ≤
      ∫ t in 0..L, |a t - b t| := by
  apply (normalLoopCurve_norm_sub_le ha hb hζ hunit hspeed hr.1).trans
  exact intervalIntegral.integral_mono_interval (le_refl 0) hr.1 hr.2
    (Filter.Eventually.of_forall (fun t => abs_nonneg (a t - b t)))
    ((ha.sub hb).abs.intervalIntegrable 0 L)

end
end TightVer401
