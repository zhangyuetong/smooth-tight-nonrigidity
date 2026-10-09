import TightVer401.NormalLoopActual
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

theorem normalLoop_hemisphere_curvature_ne_zero {ζ : ℝ → Ambient} {L : ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (hL : 0 < L) (hζL : Function.Periodic ζ L)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1)
    {e : Ambient} (hhemisphere : ∀ r, 0 < inner ℝ (ζ r) e) :
    ∃ r, normalLoopCurvature ζ r ≠ 0 := by
  by_contra h
  push Not at h
  let f : ℝ → ℝ := fun r => inner ℝ (deriv ζ r) e
  have hE := (contDiff_infty_iff_deriv.mp hζ).2
  have hd (r : ℝ) : HasDerivAt f (-inner ℝ (ζ r) e) r := by
    have hz := (hE.differentiable (by simp) r).hasDerivAt
    rw [(normalLoop_actual_frame hζ hunit hspeed r).2.2, h r,
      zero_smul, sub_zero] at hz
    have hf := hz.inner ℝ (hasDerivAt_const r e)
    simpa only [f, inner_zero_right, inner_neg_left, zero_add] using hf
  have ha : StrictAnti f := strictAnti_of_deriv_neg fun r => by
    rw [(hd r).deriv]
    exact neg_lt_zero.mpr (hhemisphere r)
  have hEL := normalLoop_derivative_periodic hζL
    (fun r => (hζ.differentiable (by simp) r).hasDerivAt)
  have he : f L = f 0 := by
    change inner ℝ (deriv ζ L) e = inner ℝ (deriv ζ 0) e
    simpa only [zero_add] using congrArg (fun v : Ambient => inner ℝ v e) (hEL 0)
  have hn := ha hL
  rw [he] at hn
  exact (lt_irrefl _) hn

theorem normalLoop_hemisphere_curvature_sq_period_pos {ζ : ℝ → Ambient} {L : ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (hL : 0 < L) (hζL : Function.Periodic ζ L)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1)
    {e : Ambient} (hhemisphere : ∀ r, 0 < inner ℝ (ζ r) e) :
    0 < ∫ r in 0..L, (normalLoopCurvature ζ r)^2 := by
  obtain ⟨r, hr⟩ := normalLoop_hemisphere_curvature_ne_zero hζ hL hζL hunit hspeed hhemisphere
  have hκ := (normalLoop_actual_smooth hζ).2.continuous
  have hκL := (normalLoop_actual_periodic hζ hζL).2
  let s := toIcoMod hL 0 r
  have hs : s ∈ Ico 0 L := toIcoMod_mem_Ico' hL r
  have he : normalLoopCurvature ζ s = normalLoopCurvature ζ r :=
    hκL.sub_zsmul_eq (toIcoDiv hL 0 r)
  have hn : 0 < (normalLoopCurvature ζ s)^2 := sq_pos_of_ne_zero (he ▸ hr)
  have hp := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    hL (continuous_const (y := (0 : ℝ))).continuousOn (hκ.pow 2).continuousOn
    (fun x _ => sq_nonneg (normalLoopCurvature ζ x))
    ⟨s, ⟨hs.1, hs.2.le⟩, hn⟩
  simpa using hp

end
end TightVer401
