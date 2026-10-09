import TightVer401.MomentSlowdownBounds

namespace TightVer401
noncomputable section
open Set Filter MeasureTheory Metric
open scoped ContDiff Topology BigOperators

theorem momentSlowdown_coordinate_bound {m n : ℕ} (V : Submodule ℝ (EuclideanSpace ℝ (Fin m)))
    (T : V ≃L[ℝ] (Fin n → ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : V, (∑ j, |T u j|) ≤ C * ‖u‖ := by
  let A := T.toContinuousLinearMap
  let C := (n : ℝ) * ‖A‖ + 1
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hA : 0 ≤ ‖A‖ := norm_nonneg A
  refine ⟨C, by dsimp [C]; positivity, fun u => ?_⟩
  have hj (j : Fin n) : |T u j| ≤ ‖A‖ * ‖u‖ := by
    calc
      |T u j| = ‖T u j‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖T u‖ := norm_le_pi_norm _ j
      _ ≤ ‖A‖ * ‖u‖ := A.le_opNorm u
  calc
    (∑ j, |T u j|) ≤ ∑ j : Fin n, ‖A‖ * ‖u‖ := Finset.sum_le_sum (fun j _ => hj j)
    _ = ((n : ℝ) * ‖A‖) * ‖u‖ := by simp; ring
    _ ≤ C * ‖u‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg u)
      dsimp [C]
      linarith

theorem momentSlowdown_bump_weight_l1_le {L a r B : ℝ} (hr : 0 < r) (b : ℝ → ℝ)
    (hleft : 0 ≤ a - r) (hright : a + r ≤ L)
    (hbound : ∀ s ∈ Icc 0 L, |b s| ≤ B) :
    (∫ s in 0..L, |momentControlBump a r hr s * b s|) ≤ 2 * B * r := by
  let β := momentControlBump a r hr
  have he : (∫ s in 0..L, β s * |b s|) = ∫ s : ℝ, β s * |b s| := by
    apply intervalIntegral.integral_eq_integral_of_support_subset
    intro s hs
    have hβ : β s ≠ 0 := by
      intro hz
      exact hs (by simp [hz])
    have hsB : s ∈ Ioo (a - r) (a + r) := by
      rw [← momentSlowdown_bump_support hr]
      exact hβ
    exact ⟨hleft.trans_lt hsB.1, hsB.2.le.trans hright⟩
  have hnorm := momentSlowdown_bump_integral_norm_le hr (fun s => |b s|) (fun s hs => by
    rw [Real.norm_eq_abs, abs_abs]
    exact hbound s ⟨hleft.trans hs.1, hs.2.trans hright⟩)
  have hnonneg : 0 ≤ ∫ s : ℝ, β s * |b s| :=
    integral_nonneg (fun s => mul_nonneg β.nonneg (abs_nonneg _))
  change ‖∫ s : ℝ, β s * |b s|‖ ≤ _ at hnorm
  rw [Real.norm_of_nonneg hnonneg, ← he] at hnorm
  have heabs : (fun s => |momentControlBump a r hr s * b s|) = fun s => β s * |b s| := by
    ext s
    rw [abs_mul, abs_of_nonneg β.nonneg]
  rw [heabs]
  nlinarith [hnorm]

theorem momentSlowdown_control_error_le {n : ℕ} (c : Fin n → ℝ) (ψ : Fin n → ℝ → ℝ)
    {K : ℝ} (hK : ∀ j s, |ψ j s| ≤ K) (s : ℝ) :
    (∑ j, |c j| * |ψ j s|) ≤ K * (∑ j, |c j|) := by
  calc
    (∑ j, |c j| * |ψ j s|) ≤ ∑ j, |c j| * K :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hK j s) (abs_nonneg _))
    _ = K * (∑ j, |c j|) := by rw [← Finset.sum_mul]; ring

theorem momentSlowdown_choose_radius {a L R ε μ η B C M K e : ℝ}
    (ha : a ∈ Ioo 0 L) (hR : 0 < R) (hε : 0 < ε) (hμ : 0 < μ) (hη : 0 < η)
    (hB : 0 < B) (hC : 0 < C) (hM : 0 < M) (hK : 0 < K) (he : 0 < e) :
    ∃ r : ℝ, 0 < r ∧ r < ε ∧ r < R ∧ r < e ∧ 0 < a - r ∧ a + r < L ∧
      2 * K * C * M * r < μ / 2 ∧ 2 * (B + C * M) * r < η := by
  let q := min ε (min R (min e (min a (min (L - a)
    (min (μ / (4 * K * C * M + 1)) (η / (2 * (B + C * M) + 1)))))))
  have ha0 : 0 < a := ha.1
  have haL : 0 < L - a := sub_pos.mpr ha.2
  have hq : 0 < q := by dsimp [q]; positivity
  obtain ⟨r, hr, hrq⟩ := exists_between hq
  have hall : r < ε ∧ r < R ∧ r < e ∧ r < a ∧ r < L - a ∧
      r < μ / (4 * K * C * M + 1) ∧ r < η / (2 * (B + C * M) + 1) := by
    simpa only [q, lt_min_iff] using hrq
  have hμden : 0 < 4 * K * C * M + 1 := by positivity
  have hηden : 0 < 2 * (B + C * M) + 1 := by positivity
  have hμr := (lt_div_iff₀ hμden).mp hall.2.2.2.2.2.1
  have hηr := (lt_div_iff₀ hηden).mp hall.2.2.2.2.2.2
  refine ⟨r, hr, hall.1, hall.2.1, hall.2.2.1, by linarith [hall.2.2.2.1],
    by linarith [hall.2.2.2.2.1], ?_, ?_⟩
  · nlinarith
  · nlinarith

end
end TightVer401
