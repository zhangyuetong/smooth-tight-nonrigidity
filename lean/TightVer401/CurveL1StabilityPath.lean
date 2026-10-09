import TightVer401.CurveL1Stability

namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff Manifold Topology
set_option backward.isDefEq.respectTransparency false

def speedLinearInterpolation (b a : ℝ → ℝ) (t r : ℝ) : ℝ :=
  (1 - t) * b r + t * a r

theorem speedLinearInterpolation_contDiff {a b : ℝ → ℝ}
    (hb : ContDiff ℝ ∞ b) (ha : ContDiff ℝ ∞ a) (t : ℝ) :
    ContDiff ℝ ∞ (speedLinearInterpolation b a t) :=
  (contDiff_const.mul hb).add (contDiff_const.mul ha)

theorem speedLinearInterpolation_periodic {a b : ℝ → ℝ} {L : ℝ}
    (hb : Function.Periodic b L) (ha : Function.Periodic a L) (t : ℝ) :
    Function.Periodic (speedLinearInterpolation b a t) L := by
  intro r
  simp only [speedLinearInterpolation, hb r, ha r]

theorem speedLinearInterpolation_positive {a b : ℝ → ℝ} {t : ℝ}
    (hb : ∀ r, 0 < b r) (ha : ∀ r, 0 < a r) (ht : t ∈ Icc 0 1) :
    ∀ r, 0 < speedLinearInterpolation b a t r := by
  intro r
  dsimp [speedLinearInterpolation]
  have h₁ := mul_nonneg (sub_nonneg.mpr ht.2) (hb r).le
  have h₂ := mul_nonneg ht.1 (ha r).le
  by_cases htz : t = 0
  · simpa only [htz, sub_zero, one_mul, zero_mul, add_zero] using hb r
  · exact h₁.trans_lt (lt_add_of_pos_right _ (mul_pos (lt_of_le_of_ne ht.1 (Ne.symm htz)) (ha r)))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem speedCurve_linearInterpolation {a b : ℝ → ℝ} {P : ℝ → E}
    (hb : Continuous b) (ha : Continuous a) (hP : Continuous P) (t r : ℝ) :
    speedCurve (speedLinearInterpolation b a t) P r =
      (1 - t) • speedCurve b P r + t • speedCurve a P r := by
  have he : (fun s => speedLinearInterpolation b a t s • P s) =
      (fun s => (1 - t) • (b s • P s) + t • (a s • P s)) := by
    funext s
    simp only [speedLinearInterpolation, add_smul, mul_smul]
  have hi₁ : IntervalIntegrable (fun s => (1 - t) • (b s • P s)) volume 0 r :=
    (((hb.smul hP).intervalIntegrable (μ := volume) 0 r).smul (1 - t))
  have hi₂ : IntervalIntegrable (fun s => t • (a s • P s)) volume 0 r :=
    (((ha.smul hP).intervalIntegrable (μ := volume) 0 r).smul t)
  unfold speedCurve rawPrimitive
  rw [he, intervalIntegral.integral_add hi₁ hi₂,
    intervalIntegral.integral_smul, intervalIntegral.integral_smul]

theorem speedLinearInterpolation_closing {a b : ℝ → ℝ} {P : ℝ → E} {L : ℝ}
    (hb : Continuous b) (ha : Continuous a) (hP : Continuous P)
    (hbc : (∫ r in 0..L, b r • P r) = 0) (hac : (∫ r in 0..L, a r • P r) = 0)
    (t : ℝ) : (∫ r in 0..L, speedLinearInterpolation b a t r • P r) = 0 := by
  have he := speedCurve_linearInterpolation hb ha hP t L
  simpa only [speedCurve, rawPrimitive, hbc, hac, smul_zero, add_zero] using he

theorem speedLinearInterpolation_L1 {a b : ℝ → ℝ}
    (hb : Continuous b) (ha : Continuous a) (L : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    (∫ r in 0..L, |speedLinearInterpolation b a t r - b r|) =
      t * ∫ r in 0..L, |a r - b r| := by
  have he (r : ℝ) : speedLinearInterpolation b a t r - b r = t * (a r - b r) := by
    unfold speedLinearInterpolation
    ring
  simp_rw [he, abs_mul, abs_of_nonneg ht]
  exact intervalIntegral.integral_const_mul t _

theorem speedLinearInterpolation_L1_le {a b : ℝ → ℝ}
    (hb : Continuous b) (ha : Continuous a) {L : ℝ} (hL : 0 ≤ L)
    {t : ℝ} (ht : t ∈ Icc 0 1) :
    (∫ r in 0..L, |speedLinearInterpolation b a t r - b r|) ≤
      ∫ r in 0..L, |a r - b r| := by
  rw [speedLinearInterpolation_L1 hb ha L ht.1]
  have hn : 0 ≤ ∫ r in 0..L, |a r - b r| :=
    intervalIntegral.integral_nonneg_of_forall hL (fun r => abs_nonneg _)
  nlinarith [ht.2]

end
end TightVer401
