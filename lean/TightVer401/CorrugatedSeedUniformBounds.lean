import TightVer401.CorrugatedSeedPartnerBounds

namespace TightVer401
noncomputable section
open Set

theorem corrugatedSeedDelta_error_periodic {N : ℝ} (hN : 1 < N) (k : ℝ) :
    Function.Periodic
      (fun t => ‖corrugatedSeedDelta k N t - Complex.I / 2 * Complex.exp ((t : ℂ) * Complex.I)‖)
      (corrugatedSeedCell N) := by
  intro t
  change ‖corrugatedSeedDelta k N (t + corrugatedSeedCell N) -
    Complex.I / 2 * Complex.exp (((t + corrugatedSeedCell N : ℝ) : ℂ) * Complex.I)‖ = _
  have he : Complex.exp (((t + corrugatedSeedCell N : ℝ) : ℂ) * Complex.I) =
      corrugatedSeedRotation N * Complex.exp ((t : ℂ) * Complex.I) := by
    simp only [Complex.ofReal_add, add_mul, Complex.exp_add, corrugatedSeedRotation]
    ring
  rw [corrugatedSeedDelta_cell hN, he]
  have hf : corrugatedSeedRotation N * corrugatedSeedDelta k N t -
      Complex.I / 2 * (corrugatedSeedRotation N * Complex.exp ((t : ℂ) * Complex.I)) =
      corrugatedSeedRotation N * (corrugatedSeedDelta k N t -
        Complex.I / 2 * Complex.exp ((t : ℂ) * Complex.I)) := by ring
  rw [hf, norm_mul]
  simp only [corrugatedSeedRotation, Complex.norm_exp_ofReal_mul_I, one_mul]

theorem corrugatedSeedDelta_uniform_error {N : ℝ} (hN : 10000 ≤ N) (k : ℝ)
    (hk : corrugatedRootIntegral (1 / N) k = 0) (t : ℝ) :
    ‖corrugatedSeedDelta k N t - Complex.I / 2 * Complex.exp ((t : ℂ) * Complex.I)‖ ≤ 100 / N := by
  have hNp : 0 < N := by linarith
  have hT : 0 < corrugatedSeedCell N := by unfold corrugatedSeedCell; positivity
  obtain ⟨n, hn, _⟩ := existsUnique_sub_zsmul_mem_Ico hT t 0
  simp only [mem_Ico, zero_add] at hn
  have h := corrugatedSeedDelta_cell_error hN k hk (t := t - n • corrugatedSeedCell N) ⟨hn.1, hn.2.le⟩
  rw [(corrugatedSeedDelta_error_periodic (by linarith : 1 < N) k).sub_zsmul_eq n] at h
  exact h

theorem corrugatedSeedPartner_uniform_error {N : ℝ} (hN : 10000 ≤ N) (t : ℝ) :
    ‖corrugatedSeedPartner N t - Complex.I / 2 * Complex.exp ((t : ℂ) * Complex.I)‖ ≤ 100 / N :=
  corrugatedSeedDelta_uniform_error hN _ (corrugatedSeedRoot_spec (by linarith)) t

theorem corrugatedSeedPartner_radius_bounds {N : ℝ} (hN : 10000 ≤ N) (t : ℝ) :
    (49 / 100 : ℝ) ≤ ‖corrugatedSeedPartner N t‖ ∧ ‖corrugatedSeedPartner N t‖ ≤ 51 / 100 := by
  have hNp : 0 < N := by linarith
  have he : 100 / N ≤ (1 / 100 : ℝ) := (div_le_div_iff₀ hNp (by norm_num)).mpr (by nlinarith)
  have h := (corrugatedSeedPartner_uniform_error hN t).trans he
  have hlim : ‖Complex.I / 2 * Complex.exp ((t : ℂ) * Complex.I)‖ = (1 / 2 : ℝ) := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    norm_num
  have hu := norm_sub_norm_le (corrugatedSeedPartner N t)
    (Complex.I / 2 * Complex.exp ((t : ℂ) * Complex.I))
  have hl := norm_sub_norm_le (Complex.I / 2 * Complex.exp ((t : ℂ) * Complex.I))
    (corrugatedSeedPartner N t)
  rw [hlim] at hu hl
  rw [norm_sub_rev] at hl
  constructor <;> linarith

end
end TightVer401
