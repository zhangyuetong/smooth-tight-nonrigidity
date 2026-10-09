import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace TightVer401
noncomputable section
open Set Filter Metric
open scoped Topology

theorem scalarReturn_uniform_ratio_bounds {R : ℝ → ℝ} {μ l u : ℝ}
    (hd : HasDerivAt R μ 0) (hzero : R 0 = 0) (hl : l < μ) (hu : μ < u) :
    ∃ e > 0, ∀ x : ℝ, x ≠ 0 → |x| < e → l < R x / x ∧ R x / x < u := by
  have ht : Tendsto (fun x : ℝ => R x / x) (𝓝[≠] 0) (𝓝 μ) := by
    have he : slope R 0 = (fun x : ℝ => R x / x) := by
      funext x
      simp only [slope_def_field, sub_zero, hzero]
    rw [← he]
    exact hd.tendsto_slope
  have he := ht.eventually (Ioo_mem_nhds hl hu)
  obtain ⟨e, he, hbound⟩ := Metric.mem_nhdsWithin_iff.mp he
  refine ⟨e, he, fun x hx hxe => ?_⟩
  exact hbound ⟨by simpa only [mem_ball, Real.dist_eq, sub_zero] using hxe,
    by simpa using hx⟩

theorem scalarReturn_exists_contraction {R : ℝ → ℝ} {μ : ℝ}
    (hd : HasDerivAt R μ 0) (hzero : R 0 = 0) (hμ : 0 < μ) (hμ1 : μ < 1) :
    ∃ (e q : ℝ), 0 < e ∧ 0 < q ∧ q < 1 ∧
      (∀ x : ℝ, |x| < e → |R x| ≤ q * |x|) ∧
      ∀ x : ℝ, x ≠ 0 → |x| < e → 0 < R x * x := by
  let q := (μ + 1) / 2
  have hq : 0 < q := by dsimp only [q]; linarith
  have hq1 : q < 1 := by dsimp only [q]; linarith
  have hμq : μ < q := by dsimp only [q]; linarith
  obtain ⟨e, he, hbound⟩ := scalarReturn_uniform_ratio_bounds hd hzero hμ hμq
  have hR (x : ℝ) (hx : x ≠ 0) : R x = (R x / x) * x := (div_mul_cancel₀ _ hx).symm
  refine ⟨e, q, he, hq, hq1, ?_, ?_⟩
  · intro x hxe
    by_cases hx : x = 0
    · simp [hx, hzero]
    · have hb := hbound x hx hxe
      rw [hR x hx, abs_mul, abs_of_pos hb.1]
      exact mul_le_mul_of_nonneg_right hb.2.le (abs_nonneg x)
  · intro x hx hxe
    have hb := hbound x hx hxe
    rw [hR x hx]
    have hs : 0 < x ^ 2 := sq_pos_of_ne_zero hx
    nlinarith [mul_pos hb.1 hs]

theorem scalarReturn_exists_expansion {R : ℝ → ℝ} {μ : ℝ}
    (hd : HasDerivAt R μ 0) (hzero : R 0 = 0) (hμ : 1 < μ) :
    ∃ (e q : ℝ), 0 < e ∧ 1 < q ∧
      ∀ x : ℝ, x ≠ 0 → |x| < e → q * |x| < |R x| ∧ 0 < R x * x := by
  let q := (μ + 1) / 2
  have hq : 1 < q := by dsimp only [q]; linarith
  have hqμ : q < μ := by dsimp only [q]; linarith
  obtain ⟨e, he, hbound⟩ := scalarReturn_uniform_ratio_bounds hd hzero hqμ (lt_add_one μ)
  refine ⟨e, q, he, hq, fun x hx hxe => ?_⟩
  have hb := hbound x hx hxe
  have hp : 0 < R x / x := lt_trans (by linarith) hb.1
  have hR : R x = (R x / x) * x := (div_mul_cancel₀ _ hx).symm
  constructor
  · rw [hR, abs_mul, abs_of_pos hp]
    exact mul_lt_mul_of_pos_right hb.1 (abs_pos.mpr hx)
  · rw [hR]
    nlinarith [mul_pos hp (sq_pos_of_ne_zero hx)]

theorem scalarReturn_contraction_iterates {R : ℝ → ℝ} {e q x : ℝ}
    (hq : 0 ≤ q) (hq1 : q < 1)
    (hbound : ∀ y : ℝ, |y| < e → |R y| ≤ q * |y|) (hx : |x| < e) :
    (∀ n : ℕ, |(R^[n]) x| < e) ∧ Tendsto (fun n : ℕ => (R^[n]) x) atTop (𝓝 0) := by
  have hi : ∀ n : ℕ, |(R^[n]) x| < e ∧ |(R^[n]) x| ≤ q^n * |x| := by
    intro n
    induction n with
    | zero => simpa using (And.intro hx (le_refl |x|))
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      have hb := hbound ((R^[n]) x) ih.1
      constructor
      · exact (hb.trans (mul_le_of_le_one_left (abs_nonneg _) hq1.le)).trans_lt ih.1
      · have he := hb.trans (mul_le_mul_of_nonneg_left ih.2 hq)
        simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using he
  refine ⟨fun n => (hi n).1, ?_⟩
  apply squeeze_zero_norm (fun n => by simpa only [Real.norm_eq_abs] using (hi n).2)
  simpa only [zero_mul] using (tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1).mul_const |x|

theorem scalarReturn_attracts {R : ℝ → ℝ} {μ : ℝ}
    (hd : HasDerivAt R μ 0) (hzero : R 0 = 0) (hμ : 0 < μ) (hμ1 : μ < 1) :
    ∃ e > 0, ∀ x : ℝ, |x| < e →
      (∀ n : ℕ, |(R^[n]) x| < e) ∧ Tendsto (fun n : ℕ => (R^[n]) x) atTop (𝓝 0) := by
  obtain ⟨e, q, he, hq, hq1, hb, _⟩ := scalarReturn_exists_contraction hd hzero hμ hμ1
  exact ⟨e, he, fun x hx => scalarReturn_contraction_iterates hq.le hq1 hb hx⟩

end
end TightVer401
