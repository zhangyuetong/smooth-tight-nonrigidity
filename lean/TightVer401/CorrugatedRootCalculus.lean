import Mathlib

namespace TightVer401
noncomputable section
open Set Filter MeasureTheory Metric
open scoped ContDiff Topology

theorem corrugated_compact_integral_hasDerivAt {F F' : ℝ → ℝ → ℝ}
    (hF : Continuous (Function.uncurry F)) (hF' : Continuous (Function.uncurry F'))
    (hd : ∀ k x, HasDerivAt (fun t => F t x) (F' k x) k)
    (a b k : ℝ) (hab : a ≤ b) :
    HasDerivAt (fun t => ∫ x in a..b, F t x) (∫ x in a..b, F' k x) k := by
  let μ := volume.restrict (Icc a b)
  haveI : IsFiniteMeasure μ := by dsimp [μ]; infer_instance
  have hf (t : ℝ) : Continuous (F t) := hF.comp (continuous_const.prodMk continuous_id)
  have hf' (t : ℝ) : Continuous (F' t) := hF'.comp (continuous_const.prodMk continuous_id)
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (s := Icc (k - 1) (k + 1) ×ˢ Icc a b) hF'.continuousOn
  have hbound : ∀ᵐ x ∂μ, ∀ t ∈ ball k 1, ‖F' t x‖ ≤ M := by
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with x hx
    intro t ht
    rw [Real.ball_eq_Ioo] at ht
    exact hM (t, x) ⟨⟨ht.1.le, ht.2.le⟩, hx⟩
  have hkey := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := F) (F' := F') (bound := fun _ => M)
    (ball_mem_nhds k zero_lt_one)
    (Filter.Eventually.of_forall (fun t => (hf t).aestronglyMeasurable))
    ((hf k).integrableOn_Icc) (hf' k).aestronglyMeasurable hbound
    (integrable_const M) (Filter.Eventually.of_forall (fun x t _ => hd t x))
  have he (t : ℝ) : (∫ x in a..b, F t x) = ∫ x, F t x ∂μ := by
    rw [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]
  have he' : (∫ x in a..b, F' k x) = ∫ x, F' k x ∂μ := by
    rw [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]
  rw [he']
  exact hkey.2.congr_of_eventuallyEq (Filter.Eventually.of_forall he)

def corrugatedWeight (ε k x : ℝ) : ℝ :=
  Real.exp (-k * Real.cos x) * (1 + ε * Real.sin x) ^ 2

def corrugatedCosMoment (ε : ℝ) (n : ℕ) (k : ℝ) : ℝ :=
  ∫ x in 0..(2 * Real.pi), corrugatedWeight ε k x * Real.cos x ^ n

def corrugatedRootIntegral (ε k : ℝ) : ℝ :=
  ∫ x in 0..(2 * Real.pi), corrugatedWeight ε k x * (1 + 2 * Real.cos x)

def corrugatedCosExpectation (ε k : ℝ) : ℝ :=
  corrugatedCosMoment ε 1 k / corrugatedCosMoment ε 0 k

theorem corrugatedWeight_continuous (ε k : ℝ) : Continuous (corrugatedWeight ε k) := by
  unfold corrugatedWeight
  fun_prop

theorem corrugatedWeight_pos {ε : ℝ} (hε : |ε| < 1) (k x : ℝ) :
    0 < corrugatedWeight ε k x := by
  have hsin : |Real.sin x| ≤ 1 := Real.abs_sin_le_one x
  have hterm : |ε * Real.sin x| < 1 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hsin (abs_nonneg ε)).trans_lt (by simpa using hε)
  have hbase : 0 < 1 + ε * Real.sin x := by linarith [neg_abs_le (ε * Real.sin x)]
  exact mul_pos (Real.exp_pos _) (sq_pos_of_pos hbase)

theorem corrugatedCosMoment_continuous (ε : ℝ) (n : ℕ) :
    Continuous (corrugatedCosMoment ε n) := by
  have hF : Continuous (Function.uncurry
      (fun k x : ℝ => corrugatedWeight ε k x * Real.cos x ^ n)) := by
    unfold Function.uncurry corrugatedWeight
    fun_prop
  have hc := continuous_parametric_integral_of_continuous (μ := volume)
    (s := Icc 0 (2 * Real.pi)) hF isCompact_Icc
  have he (k : ℝ) : corrugatedCosMoment ε n k =
      ∫ x in Icc 0 (2 * Real.pi), corrugatedWeight ε k x * Real.cos x ^ n := by
    rw [corrugatedCosMoment, intervalIntegral.integral_of_le (by positivity), integral_Icc_eq_integral_Ioc]
  have hefun : corrugatedCosMoment ε n =
      (fun k => ∫ x in Icc 0 (2 * Real.pi), corrugatedWeight ε k x * Real.cos x ^ n) := funext he
  rw [hefun]
  exact hc

theorem corrugatedCosMoment_hasDerivAt (ε : ℝ) (n : ℕ) (k : ℝ) :
    HasDerivAt (corrugatedCosMoment ε n) (-corrugatedCosMoment ε (n + 1) k) k := by
  have hF : Continuous (Function.uncurry
      (fun k x : ℝ => corrugatedWeight ε k x * Real.cos x ^ n)) := by
    unfold Function.uncurry corrugatedWeight
    fun_prop
  have hF' : Continuous (Function.uncurry (fun k x : ℝ =>
      -(corrugatedWeight ε k x * Real.cos x ^ (n + 1)))) := by
    unfold Function.uncurry corrugatedWeight
    fun_prop
  have hd (t x : ℝ) : HasDerivAt
      (fun t => corrugatedWeight ε t x * Real.cos x ^ n)
      (-(corrugatedWeight ε t x * Real.cos x ^ (n + 1))) t := by
    have h := ((((hasDerivAt_id t).neg.mul_const (Real.cos x)).exp).mul_const
      ((1 + ε * Real.sin x) ^ 2)).mul_const (Real.cos x ^ n)
    have h' := h.congr_of_eventuallyEq (f₁ := fun t => corrugatedWeight ε t x * Real.cos x ^ n)
      (Filter.Eventually.of_forall (fun y => by rfl))
    have he : Real.exp (-t * Real.cos x) * (-1 * Real.cos x) *
        (1 + ε * Real.sin x) ^ 2 * Real.cos x ^ n =
        -(corrugatedWeight ε t x * Real.cos x ^ (n + 1)) := by
      simp only [corrugatedWeight, pow_succ]
      ring
    exact he ▸ h'
  have h := corrugated_compact_integral_hasDerivAt hF hF' hd 0 (2 * Real.pi) k (by positivity)
  change HasDerivAt (fun t => ∫ x in 0..(2 * Real.pi), corrugatedWeight ε t x * Real.cos x ^ n)
    (-(∫ x in 0..(2 * Real.pi), corrugatedWeight ε k x * Real.cos x ^ (n + 1))) k
  simpa only [intervalIntegral.integral_neg] using h

theorem corrugatedCosMoment_zero_pos {ε : ℝ} (hε : |ε| < 1) (k : ℝ) :
    0 < corrugatedCosMoment ε 0 k := by
  simp only [corrugatedCosMoment, pow_zero, mul_one]
  have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (show 0 < 2 * Real.pi by positivity) continuous_const.continuousOn
    (corrugatedWeight_continuous ε k).continuousOn
    (fun x _ => (corrugatedWeight_pos hε k x).le)
    ⟨0, ⟨le_rfl, by positivity⟩, corrugatedWeight_pos hε k 0⟩
  simpa only [intervalIntegral.integral_zero] using h

theorem corrugatedRootIntegral_eq (ε k : ℝ) :
    corrugatedRootIntegral ε k = corrugatedCosMoment ε 0 k + 2 * corrugatedCosMoment ε 1 k := by
  have h := corrugatedWeight_continuous ε k
  unfold corrugatedRootIntegral corrugatedCosMoment
  simp only [pow_zero, pow_one, mul_one]
  have he : (fun x => corrugatedWeight ε k x * (1 + 2 * Real.cos x)) =
      (fun x => corrugatedWeight ε k x + 2 * (corrugatedWeight ε k x * Real.cos x)) := by
    ext x
    ring
  rw [he]
  have hi : IntervalIntegrable (fun x => 2 * (corrugatedWeight ε k x * Real.cos x)) volume 0 (2 * Real.pi) :=
    ((continuous_const (y := (2 : ℝ))).mul (h.mul Real.continuous_cos)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (h.intervalIntegrable _ _) hi,
    intervalIntegral.integral_const_mul]

theorem corrugatedRootIntegral_zero_iff {ε : ℝ} (hε : |ε| < 1) (k : ℝ) :
    corrugatedRootIntegral ε k = 0 ↔ corrugatedCosExpectation ε k = -1 / 2 := by
  rw [corrugatedRootIntegral_eq, corrugatedCosExpectation, div_eq_iff
    (corrugatedCosMoment_zero_pos hε k).ne']
  constructor <;> intro h <;> linarith

theorem corrugatedCosExpectation_hasDerivAt {ε : ℝ} (hε : |ε| < 1) (k : ℝ) :
    HasDerivAt (corrugatedCosExpectation ε)
      (-(corrugatedCosMoment ε 2 k / corrugatedCosMoment ε 0 k -
        (corrugatedCosExpectation ε k) ^ 2)) k := by
  have h := (corrugatedCosMoment_hasDerivAt ε 1 k).div
    (corrugatedCosMoment_hasDerivAt ε 0 k) (corrugatedCosMoment_zero_pos hε k).ne'
  have h' := h.congr_of_eventuallyEq (f₁ := corrugatedCosExpectation ε)
    (Filter.Eventually.of_forall (fun t => by rfl))
  have he : (-corrugatedCosMoment ε (1 + 1) k * corrugatedCosMoment ε 0 k -
      corrugatedCosMoment ε 1 k * -corrugatedCosMoment ε (0 + 1) k) /
      corrugatedCosMoment ε 0 k ^ 2 =
      -(corrugatedCosMoment ε 2 k / corrugatedCosMoment ε 0 k -
        corrugatedCosExpectation ε k ^ 2) := by
    unfold corrugatedCosExpectation
    field_simp
    ring
  exact he ▸ h'

end
end TightVer401
