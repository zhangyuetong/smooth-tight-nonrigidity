import TightVer401.CorrugatedSeedCellAverage

namespace TightVer401
noncomputable section

theorem corrugated_exponential_quotient_bounds {α : ℝ} (hα : 0 < α) (hsmall : α ≤ 1 / 100) :
    ‖(α : ℂ) / (Complex.exp ((α : ℂ) * Complex.I) - 1)‖ ≤ 11 / 10 ∧
      ‖(α : ℂ) / (Complex.exp ((α : ℂ) * Complex.I) - 1) + Complex.I‖ ≤ (11 / 10) * α := by
  let e := Complex.exp ((α : ℂ) * Complex.I) - 1
  let R := e - (α : ℂ) * Complex.I
  have hR : ‖R‖ ≤ α^2 := by
    have h := Complex.norm_exp_sub_one_sub_id_le
      (x := (α : ℂ) * Complex.I) (by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one,
          abs_of_pos hα]
        linarith)
    simpa only [R, e, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
      mul_one, abs_of_pos hα] using h
  have hαnorm : α ≤ ‖e‖ + ‖R‖ := by
    have h := norm_sub_le e R
    have he : e - R = (α : ℂ) * Complex.I := by dsimp [R]; ring
    rw [he] at h
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
      mul_one, abs_of_pos hα] using h
  have heLower : (99 / 100 : ℝ) * α ≤ ‖e‖ := by nlinarith
  have hep : 0 < ‖e‖ := lt_of_lt_of_le (by positivity) heLower
  have he0 : e ≠ 0 := norm_pos_iff.mp hep
  have hQ : ‖(α : ℂ) / e‖ ≤ 11 / 10 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hα]
    apply (div_le_iff₀ hep).mpr
    nlinarith
  have hQi : (α : ℂ) / e + Complex.I = Complex.I * R / e := by
    apply (eq_div_iff he0).mpr
    simp only [R]
    field_simp
    ring_nf
    simp [Complex.I_sq]
  have hD : ‖(α : ℂ) / e + Complex.I‖ ≤ (11 / 10) * α := by
    rw [hQi, norm_div, norm_mul, Complex.norm_I, one_mul]
    apply (div_le_iff₀ hep).mpr
    nlinarith
  exact ⟨hQ, hD⟩

theorem corrugatedSeedCellQuotient_bounds {N : ℝ} (hN : 10000 ≤ N) :
    ‖corrugatedSeedCellQuotient N‖ ≤ 11 / 10 ∧
      ‖corrugatedSeedCellQuotient N + Complex.I‖ ≤ 9 / N := by
  have hNp : 0 < N := by linarith
  have hα : 0 < corrugatedSeedCell N := by unfold corrugatedSeedCell; positivity
  have hsmall : corrugatedSeedCell N ≤ 1 / 100 := by
    unfold corrugatedSeedCell
    apply (div_le_iff₀ hNp).mpr
    linarith [Real.pi_lt_four]
  have h := corrugated_exponential_quotient_bounds hα hsmall
  refine ⟨h.1, h.2.trans ?_⟩
  unfold corrugatedSeedCell
  apply (le_div_iff₀ hNp).mpr
  have he : (11 / 10 : ℝ) * (2 * Real.pi / N) * N = (11 / 10) * (2 * Real.pi) := by
    field_simp
  rw [he]
  linarith [Real.pi_lt_four]

end
end TightVer401
