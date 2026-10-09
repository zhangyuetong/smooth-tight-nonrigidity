import TightVer401.NormalLoopGlobalArclength

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false in
theorem normalLoop_constant_curvature_axis {ζ : ℝ → Ambient}
    (hζ : ContDiff ℝ ∞ ζ) (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1)
    {c : ℝ} (hκ : ∀ r, normalLoopCurvature ζ r = c) :
    ∀ r, normalLoopTangent ζ r - c • ζ r = normalLoopTangent ζ 0 - c • ζ 0 := by
  have hzero (r : ℝ) : HasDerivAt (normalLoopTangent ζ - c • ζ) 0 r := by
    have hP := (normalLoop_actual_frame hζ hunit hspeed r).2.1
    have hZ := ((hζ.contDiffAt (x := r)).differentiableAt (by simp)).hasDerivAt
    have hd := hP.sub (hZ.const_smul c)
    simpa only [hκ r, sub_self] using hd
  intro r
  have he := is_const_of_deriv_eq_zero (fun r => (hzero r).differentiableAt)
    (fun r => (hzero r).deriv) r 0
  simpa only [Pi.sub_apply, Pi.smul_apply] using he

theorem normalLoop_closure_forces_nonconstant_curvature {ζ : ℝ → Ambient} {a : ℝ → ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (ha : Continuous a)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1)
    (hpos : ∀ r, 0 < a r) {L : ℝ} (hL : 0 < L)
    (hmoment : normalLoopMoment a ζ (deriv ζ) L = 0) :
    ∃ r, normalLoopCurvature ζ r ≠ normalLoopCurvature ζ 0 := by
  by_contra h
  push Not at h
  let c := normalLoopCurvature ζ 0
  let C := normalLoopTangent ζ 0 - c • ζ 0
  have haxis := normalLoop_constant_curvature_axis hζ hunit hspeed h
  have hpair (r : ℝ) : inner ℝ C (normalLoopTangent ζ r) = 1 := by
    change inner ℝ (normalLoopTangent ζ 0 - c • ζ 0) (normalLoopTangent ζ r) = 1
    rw [← haxis r]
    have hf := (normalLoop_actual_frame hζ hunit hspeed r).1
    have hn : inner ℝ (ζ r) (normalLoopTangent ζ r) = 0 := by
      rw [real_inner_comm]
      exact hf.2.2.2.2.1
    rw [inner_sub_left, real_inner_smul_left, hf.1, hn, mul_zero, sub_zero]
  have hP := (normalLoop_actual_smooth hζ).1.continuous
  have hI : IntervalIntegrable (fun r => a r • normalLoopTangent ζ r) MeasureTheory.volume 0 L :=
    (ha.smul hP).intervalIntegrable 0 L
  have hint := (innerSL ℝ C).intervalIntegral_comp_comm hI
  change (∫ r in 0..L, inner ℝ C (a r • normalLoopTangent ζ r)) =
    inner ℝ C (normalLoopMoment a ζ (deriv ζ) L) at hint
  rw [hmoment, inner_zero_right] at hint
  have hzero : (∫ r in 0..L, a r) = 0 := by
    simpa only [real_inner_smul_right, hpair, mul_one] using hint
  have hp := normalLoop_arclength_period_pos ha hpos hL
  change 0 < (∫ r in 0..L, a r) at hp
  linarith

end
end TightVer401
