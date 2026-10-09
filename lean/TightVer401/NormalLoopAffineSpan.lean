import TightVer401.NormalLoopSpan
import Mathlib.Analysis.Normed.Affine.AddTorsorBases

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff

theorem normalLoop_closure_constant_pairing_eq_zero {ζ : ℝ → Ambient} {a : ℝ → ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (ha : Continuous a) (hpos : ∀ r, 0 < a r)
    {L : ℝ} (hL : 0 < L) (hmoment : normalLoopMoment a ζ (deriv ζ) L = 0)
    {v : Ambient} {c : ℝ} (hv : ∀ r, inner ℝ v (normalLoopTangent ζ r) = c) : c = 0 := by
  have hP := (normalLoop_actual_smooth hζ).1.continuous
  have hI : IntervalIntegrable (fun r => a r • normalLoopTangent ζ r) MeasureTheory.volume 0 L :=
    (ha.smul hP).intervalIntegrable 0 L
  have hint := (innerSL ℝ v).intervalIntegral_comp_comm hI
  change (∫ r in 0..L, inner ℝ v (a r • normalLoopTangent ζ r)) =
    inner ℝ v (normalLoopMoment a ζ (deriv ζ) L) at hint
  rw [hmoment, inner_zero_right] at hint
  simp only [real_inner_smul_right, hv, intervalIntegral.integral_mul_const] at hint
  have hp := normalLoop_arclength_period_pos ha hpos hL
  change 0 < (∫ r in 0..L, a r) at hp
  exact (mul_eq_zero.mp hint).resolve_left hp.ne'

theorem normalLoop_closure_affineSpan_eq_top {ζ : ℝ → Ambient} {a : ℝ → ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (ha : Continuous a)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1)
    (hpos : ∀ r, 0 < a r) {L : ℝ} (hL : 0 < L)
    (hmoment : normalLoopMoment a ζ (deriv ζ) L = 0) :
    affineSpan ℝ (Set.range (normalLoopTangent ζ)) = ⊤ := by
  rw [AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ Ambient Ambient (Set.range_nonempty _),
    vectorSpan_range_eq_span_range_vsub_right ℝ (normalLoopTangent ζ) 0]
  apply Submodule.orthogonal_eq_bot_iff.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro v hv
  have hc (r : ℝ) : inner ℝ v (normalLoopTangent ζ r) = inner ℝ v (normalLoopTangent ζ 0) := by
    have he := Submodule.inner_left_of_mem_orthogonal
      (Submodule.subset_span (Set.mem_range_self r)) hv
    change inner ℝ v (normalLoopTangent ζ r - normalLoopTangent ζ 0) = 0 at he
    rw [inner_sub_right, sub_eq_zero] at he
    exact he
  have hcz := normalLoop_closure_constant_pairing_eq_zero hζ ha hpos hL hmoment hc
  exact normalLoop_closure_annihilator_eq_zero hζ ha hunit hspeed hpos hL hmoment
    (fun r => (hc r).trans hcz)

end
end TightVer401
