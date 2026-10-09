import TightVer401.CorrugatedRootCalculus

namespace TightVer401
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology

def corrugatedCenteredSecondMoment (ε k c : ℝ) : ℝ :=
  ∫ x in 0..(2 * Real.pi), corrugatedWeight ε k x * (Real.cos x - c) ^ 2

theorem corrugatedCenteredSecondMoment_pos {ε : ℝ} (hε : |ε| < 1) (k c : ℝ) :
    0 < corrugatedCenteredSecondMoment ε k c := by
  have hc : Continuous (fun x => corrugatedWeight ε k x * (Real.cos x - c) ^ 2) :=
    (corrugatedWeight_continuous ε k).mul ((Real.continuous_cos.sub continuous_const).pow 2)
  have hex : ∃ x ∈ Icc 0 (2 * Real.pi),
      0 < corrugatedWeight ε k x * (Real.cos x - c) ^ 2 := by
    by_cases hc1 : c = 1
    · refine ⟨Real.pi, ⟨Real.pi_pos.le, by linarith [Real.pi_pos]⟩, ?_⟩
      rw [Real.cos_pi, hc1]
      exact mul_pos (corrugatedWeight_pos hε k Real.pi) (by norm_num)
    · refine ⟨0, ⟨le_rfl, by positivity⟩, ?_⟩
      apply mul_pos (corrugatedWeight_pos hε k 0)
      rw [Real.cos_zero]
      exact sq_pos_of_ne_zero (sub_ne_zero.mpr (fun h => hc1 h.symm))
  have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (show 0 < 2 * Real.pi by positivity) continuous_const.continuousOn hc.continuousOn
    (fun x _ => mul_nonneg (corrugatedWeight_pos hε k x).le (sq_nonneg _)) hex
  simpa only [corrugatedCenteredSecondMoment, intervalIntegral.integral_zero] using h

theorem corrugatedCenteredSecondMoment_eq (ε k c : ℝ) :
    corrugatedCenteredSecondMoment ε k c = corrugatedCosMoment ε 2 k -
      (2 * c) * corrugatedCosMoment ε 1 k + c ^ 2 * corrugatedCosMoment ε 0 k := by
  have hw := corrugatedWeight_continuous ε k
  have hi₂ : IntervalIntegrable (fun x => corrugatedWeight ε k x * Real.cos x ^ 2)
      volume 0 (2 * Real.pi) := (hw.mul (Real.continuous_cos.pow 2)).intervalIntegrable _ _
  have hi₁ : IntervalIntegrable (fun x => (2 * c) * (corrugatedWeight ε k x * Real.cos x))
      volume 0 (2 * Real.pi) :=
    ((continuous_const (y := 2 * c)).mul (hw.mul Real.continuous_cos)).intervalIntegrable _ _
  have hi₀ : IntervalIntegrable (fun x => c ^ 2 * corrugatedWeight ε k x)
      volume 0 (2 * Real.pi) :=
    ((continuous_const (y := c ^ 2)).mul hw).intervalIntegrable _ _
  have he : (fun x => corrugatedWeight ε k x * (Real.cos x - c) ^ 2) =
      (fun x => corrugatedWeight ε k x * Real.cos x ^ 2 -
        (2 * c) * (corrugatedWeight ε k x * Real.cos x) + c ^ 2 * corrugatedWeight ε k x) := by
    ext x
    ring
  unfold corrugatedCenteredSecondMoment corrugatedCosMoment
  rw [he, intervalIntegral.integral_add (hi₂.sub hi₁) hi₀,
    intervalIntegral.integral_sub hi₂ hi₁]
  simp only [pow_one, pow_zero, mul_one, intervalIntegral.integral_const_mul]

theorem corrugated_variance_pos {ε : ℝ} (hε : |ε| < 1) (k : ℝ) :
    0 < corrugatedCosMoment ε 2 k / corrugatedCosMoment ε 0 k -
      (corrugatedCosExpectation ε k) ^ 2 := by
  have hz := corrugatedCosMoment_zero_pos hε k
  have hp := corrugatedCenteredSecondMoment_pos hε k (corrugatedCosExpectation ε k)
  have he : corrugatedCenteredSecondMoment ε k (corrugatedCosExpectation ε k) =
      corrugatedCosMoment ε 0 k *
        (corrugatedCosMoment ε 2 k / corrugatedCosMoment ε 0 k -
          corrugatedCosExpectation ε k ^ 2) := by
    rw [corrugatedCenteredSecondMoment_eq]
    unfold corrugatedCosExpectation
    field_simp [hz.ne']
    ring
  rw [he] at hp
  exact (mul_pos_iff_of_pos_left hz).mp hp

theorem corrugatedCosExpectation_strictAnti {ε : ℝ} (hε : |ε| < 1) :
    StrictAnti (corrugatedCosExpectation ε) := by
  apply strictAnti_of_hasDerivAt_neg (corrugatedCosExpectation_hasDerivAt hε)
  intro k
  exact neg_neg_of_pos (corrugated_variance_pos hε k)

theorem corrugatedRootIntegral_unique {ε : ℝ} (hε : |ε| < 1) {k₁ k₂ : ℝ}
    (h₁ : corrugatedRootIntegral ε k₁ = 0) (h₂ : corrugatedRootIntegral ε k₂ = 0) : k₁ = k₂ := by
  apply (corrugatedCosExpectation_strictAnti hε).injective
  exact ((corrugatedRootIntegral_zero_iff hε k₁).mp h₁).trans
    ((corrugatedRootIntegral_zero_iff hε k₂).mp h₂).symm

end
end TightVer401
