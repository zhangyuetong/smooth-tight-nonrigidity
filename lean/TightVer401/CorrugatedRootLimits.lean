import TightVer401.CorrugatedRootTiltLimit
import TightVer401.CorrugatedRootVariance

namespace TightVer401
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology

def corrugatedBaseWeight (ε x : ℝ) : ℝ := (1 + ε * Real.sin x) ^ 2

theorem corrugatedBaseWeight_bounds {ε : ℝ} (hε : |ε| < 1) (x : ℝ) :
    (1 - |ε|) ^ 2 ≤ corrugatedBaseWeight ε x ∧
      corrugatedBaseWeight ε x ≤ (1 + |ε|) ^ 2 := by
  have hs : |ε * Real.sin x| ≤ |ε| := by
    rw [abs_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.abs_sin_le_one x) (abs_nonneg ε)
  have hlo := neg_abs_le (ε * Real.sin x)
  have hhi := le_abs_self (ε * Real.sin x)
  have hlow : 0 ≤ 1 - |ε| := by linarith
  unfold corrugatedBaseWeight
  constructor <;> nlinarith [abs_nonneg ε]

theorem corrugatedBaseWeight_continuous (ε : ℝ) : Continuous (corrugatedBaseWeight ε) := by
  unfold corrugatedBaseWeight
  fun_prop

theorem corrugatedTiltMass_eq (ε k s : ℝ) :
    compactTiltMass (2 * Real.pi) (corrugatedBaseWeight ε) (fun x => 1 + s * Real.cos x) k =
      Real.exp (-k) * corrugatedCosMoment ε 0 (s * k) := by
  have he (x : ℝ) : corrugatedBaseWeight ε x * Real.exp (-k * (1 + s * Real.cos x)) =
      Real.exp (-k) * corrugatedWeight ε (s * k) x := by
    have hex : -k * (1 + s * Real.cos x) = -k + (-(s * k) * Real.cos x) := by ring
    rw [hex, Real.exp_add]
    simp only [corrugatedBaseWeight, corrugatedWeight]
    ring
  unfold compactTiltMass corrugatedCosMoment
  simp only [pow_zero, mul_one, he, intervalIntegral.integral_const_mul]

theorem corrugatedTiltFirst_eq (ε k s : ℝ) :
    compactTiltFirst (2 * Real.pi) (corrugatedBaseWeight ε) (fun x => 1 + s * Real.cos x) k =
      Real.exp (-k) * (corrugatedCosMoment ε 0 (s * k) + s * corrugatedCosMoment ε 1 (s * k)) := by
  have he (x : ℝ) : corrugatedBaseWeight ε x * Real.exp (-k * (1 + s * Real.cos x)) *
      (1 + s * Real.cos x) = Real.exp (-k) * (corrugatedWeight ε (s * k) x +
        s * (corrugatedWeight ε (s * k) x * Real.cos x)) := by
    have hex : -k * (1 + s * Real.cos x) = -k + (-(s * k) * Real.cos x) := by ring
    rw [hex, Real.exp_add]
    simp only [corrugatedBaseWeight, corrugatedWeight]
    ring
  have hw := corrugatedWeight_continuous ε (s * k)
  have hi : IntervalIntegrable (fun x => s * (corrugatedWeight ε (s * k) x * Real.cos x))
      volume 0 (2 * Real.pi) :=
    ((continuous_const (y := s)).mul (hw.mul Real.continuous_cos)).intervalIntegrable _ _
  unfold compactTiltFirst corrugatedCosMoment
  simp only [he, pow_zero, pow_one, mul_one]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hw.intervalIntegrable _ _) hi,
    intervalIntegral.integral_const_mul]

theorem corrugatedTilt_ratio_eq {ε : ℝ} (hε : |ε| < 1) (k s : ℝ) :
    compactTiltFirst (2 * Real.pi) (corrugatedBaseWeight ε) (fun x => 1 + s * Real.cos x) k /
      compactTiltMass (2 * Real.pi) (corrugatedBaseWeight ε) (fun x => 1 + s * Real.cos x) k =
      1 + s * corrugatedCosExpectation ε (s * k) := by
  rw [corrugatedTiltFirst_eq, corrugatedTiltMass_eq]
  unfold corrugatedCosExpectation
  rw [mul_div_mul_left _ _ (Real.exp_pos (-k)).ne', add_div,
    div_self (corrugatedCosMoment_zero_pos hε (s * k)).ne', mul_div_assoc]

theorem corrugatedCosExpectation_tendsto_atTop {ε : ℝ} (hε : |ε| < 1) :
    Tendsto (corrugatedCosExpectation ε) atTop (𝓝 (-1)) := by
  have hA : 0 < (1 - |ε|) ^ 2 := sq_pos_of_pos (sub_pos.mpr hε)
  have h := compactTiltFirst_ratio_tendsto_zero (u := fun x => 1 + Real.cos x)
    (corrugatedBaseWeight_continuous ε)
    (continuous_const.add Real.continuous_cos) (show 0 < 2 * Real.pi by positivity) hA
    (sq_nonneg (1 + |ε|))
    (fun x _ => ⟨(corrugatedBaseWeight_bounds hε x).1, (corrugatedBaseWeight_bounds hε x).2,
      ⟨by linarith [Real.neg_one_le_cos x], by linarith [Real.cos_le_one x]⟩⟩)
    (show Real.pi ∈ Icc 0 (2 * Real.pi) from ⟨Real.pi_pos.le, by linarith [Real.pi_pos]⟩)
    (show 1 + Real.cos Real.pi = 0 by simp)
  have he (k : ℝ) : compactTiltFirst (2 * Real.pi) (corrugatedBaseWeight ε)
      (fun x => 1 + Real.cos x) k / compactTiltMass (2 * Real.pi)
      (corrugatedBaseWeight ε) (fun x => 1 + Real.cos x) k = 1 + corrugatedCosExpectation ε k := by
    simpa only [one_mul] using corrugatedTilt_ratio_eq hε k 1
  have ht := h.congr he
  have ht' := ht.sub_const 1
  have hout := ht'.congr (fun k => by ring)
  simpa only [zero_sub] using hout

theorem corrugatedCosExpectation_tendsto_atBot {ε : ℝ} (hε : |ε| < 1) :
    Tendsto (corrugatedCosExpectation ε) atBot (𝓝 1) := by
  have hA : 0 < (1 - |ε|) ^ 2 := sq_pos_of_pos (sub_pos.mpr hε)
  have h := compactTiltFirst_ratio_tendsto_zero (u := fun x => 1 - Real.cos x)
    (corrugatedBaseWeight_continuous ε)
    (continuous_const.sub Real.continuous_cos) (show 0 < 2 * Real.pi by positivity) hA
    (sq_nonneg (1 + |ε|))
    (fun x _ => ⟨(corrugatedBaseWeight_bounds hε x).1, (corrugatedBaseWeight_bounds hε x).2,
      ⟨by linarith [Real.cos_le_one x], by linarith [Real.neg_one_le_cos x]⟩⟩)
    (show (0 : ℝ) ∈ Icc 0 (2 * Real.pi) from ⟨le_rfl, by positivity⟩)
    (show 1 - Real.cos 0 = 0 by simp)
  have he (k : ℝ) : compactTiltFirst (2 * Real.pi) (corrugatedBaseWeight ε)
      (fun x => 1 - Real.cos x) k / compactTiltMass (2 * Real.pi)
      (corrugatedBaseWeight ε) (fun x => 1 - Real.cos x) k = 1 - corrugatedCosExpectation ε (-k) := by
    simpa only [neg_one_mul, one_mul, add_neg_cancel_left, sub_eq_add_neg] using corrugatedTilt_ratio_eq hε k (-1)
  have ht := h.congr he
  have ht' := (tendsto_const_nhds (x := (1 : ℝ))).sub ht
  have ht'' : Tendsto (fun k => corrugatedCosExpectation ε (-k)) atTop (𝓝 1) := by
    have hout := ht'.congr (fun k => by ring)
    simpa only [sub_zero] using hout
  have hout := ht''.comp tendsto_neg_atBot_atTop
  simpa only [Function.comp_def, neg_neg] using hout

end
end TightVer401
