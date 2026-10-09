import OAI.Geometry.SurfaceImmersion.Primitive.PeriodicPrimitive

namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.ClosedSurfaceR4.PeriodicPrimitive
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def speedCurve (a : ℝ → ℝ) (P : ℝ → E) : ℝ → E := rawPrimitive (fun x => a x • P x)

theorem speedCurve_increment {a : ℝ → ℝ} {P : ℝ → E}
    (ha : Continuous a) (hP : Continuous P) (x y : ℝ) :
    speedCurve a P y - speedCurve a P x = ∫ t in x..y, a t • P t := by
  have h := intervalIntegral.integral_add_adjacent_intervals
    ((ha.smul hP).intervalIntegrable (μ := volume) 0 x)
    ((ha.smul hP).intervalIntegrable (μ := volume) x y)
  simp only [Pi.smul_apply'] at h
  change (∫ t in 0..y, a t • P t) - (∫ t in 0..x, a t • P t) = _
  rw [← h]
  abel

theorem speedCurve_uniform_norm_sub_le {a b : ℝ → ℝ} {P : ℝ → E}
    (ha : Continuous a) (hb : Continuous b) (hP : Continuous P) {L M : ℝ}
    (hM : 0 ≤ M) (hbound : ∀ x ∈ Icc 0 L, ‖P x‖ ≤ M) {r : ℝ} (hr : r ∈ Icc 0 L) :
    ‖speedCurve a P r - speedCurve b P r‖ ≤ M * ∫ t in 0..L, |a t - b t| := by
  have he : speedCurve a P r - speedCurve b P r = ∫ t in 0..r, (a t - b t) • P t := by
    dsimp [speedCurve, rawPrimitive]
    have hs := intervalIntegral.integral_sub ((ha.smul hP).intervalIntegrable (μ := volume) 0 r)
      ((hb.smul hP).intervalIntegrable (μ := volume) 0 r)
    simp only [Pi.smul_apply', Pi.sub_apply] at hs
    rw [← hs]
    simp only [sub_smul]
  rw [he]
  apply (intervalIntegral.norm_integral_le_integral_norm hr.1).trans
  have hi := ((ha.sub hb).abs.mul (continuous_const (y := M))).intervalIntegrable (μ := volume) 0 r
  have hn := intervalIntegral.integral_mono_on hr.1
    (((ha.sub hb).smul hP).norm.intervalIntegrable 0 r) hi
    (fun x hx => by
      change ‖(a x - b x) • P x‖ ≤ |a x - b x| * M
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hbound x ⟨hx.1, hx.2.trans hr.2⟩) (abs_nonneg _))
  apply hn.trans
  change (∫ x in 0..r, |a x - b x| * M) ≤ M * ∫ t in 0..L, |a t - b t|
  rw [intervalIntegral.integral_mul_const, mul_comm]
  apply mul_le_mul_of_nonneg_left _ hM
  exact intervalIntegral.integral_mono_interval (le_refl 0) hr.1 hr.2
    (Filter.Eventually.of_forall (fun t => abs_nonneg (a t - b t)))
    ((ha.sub hb).abs.intervalIntegrable 0 L)

theorem exists_speedCurve_uniform_bound (P : ℝ → E) (hP : Continuous P) (L : ℝ) :
    ∃ M > 0, ∀ x ∈ Icc 0 L, ‖P x‖ ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hP.continuousOn
  exact ⟨max M 1, zero_lt_one.trans_le (le_max_right _ _),
    fun x hx => (hM x hx).trans (le_max_left _ _)⟩

end
end TightVer401
