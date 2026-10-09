import TightVer401.MomentControlCoefficients

namespace TightVer401
noncomputable section
open Set Filter MeasureTheory Metric
open scoped ContDiff Topology

def slowdownControl (a r : ℝ) (hr : 0 < r) (b : ℝ → ℝ) : ℝ → ℝ :=
  fun x => momentControlBump a r hr x * b x

def slowdownVectorMoment {m : ℕ} (L a r : ℝ) (hr : 0 < r) (b : ℝ → ℝ)
    (f : ℝ → EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin m) :=
  ∫ x in 0..L, slowdownControl a r hr b x • f x

theorem slowdownControl_support {L a r : ℝ} (hr : 0 < r) (b : ℝ → ℝ)
    (hleft : 0 ≤ a - r) (hright : a + r ≤ L) :
    Function.support (slowdownControl a r hr b) ⊆ Ioo 0 L := by
  intro x hx
  have hxβ : momentControlBump a r hr x ≠ 0 := by
    intro hz
    apply hx
    simp [slowdownControl, hz]
  have hxball : x ∈ ball a r := by
    have hxSupport : x ∈ Function.support (momentControlBump a r hr : ℝ → ℝ) := hxβ
    rw [(momentControlBump a r hr).support_eq] at hxSupport
    exact hxSupport
  rw [Real.ball_eq_Ioo] at hxball
  exact ⟨hleft.trans_lt hxball.1, hxball.2.trans_le hright⟩

theorem slowdownVectorMoment_mem_span {m : ℕ} {f : ℝ → EuclideanSpace ℝ (Fin m)}
    {L a r : ℝ} (hr : 0 < r) (b : ℝ → ℝ) (hleft : 0 ≤ a - r) (hright : a + r ≤ L) :
    slowdownVectorMoment L a r hr b f ∈ momentSampleSpan f (Ioo 0 L) :=
  controlMoment_interval_mem_span (slowdownControl_support hr b hleft hright)

theorem norm_slowdown_real_moment_le {m : ℕ} {f : ℝ → EuclideanSpace ℝ (Fin m)}
    {a r M : ℝ} (hr : 0 < r) (b : ℝ → ℝ) (hM : 0 ≤ M)
    (hbound : ∀ x ∈ closedBall a r, ‖b x • f x‖ ≤ M) :
    ‖realControlMoment f (slowdownControl a r hr b)‖ ≤ 2 * M * r := by
  let β := momentControlBump a r hr
  have hβr : β.rOut = r := rfl
  have hpoint (x : ℝ) : ‖slowdownControl a r hr b x • f x‖ ≤ β x * M := by
    by_cases hx : x ∈ ball a r
    · change ‖(β x * b x) • f x‖ ≤ _
      rw [mul_smul, norm_smul, Real.norm_of_nonneg β.nonneg]
      exact mul_le_mul_of_nonneg_left (hbound x (ball_subset_closedBall hx)) β.nonneg
    · have hxzero : β x = 0 := β.zero_of_le_dist (not_lt.mp hx)
      change ‖(β x * b x) • f x‖ ≤ β x * M
      rw [hxzero]
      simp
  have hnorm : ‖∫ x, slowdownControl a r hr b x • f x‖ ≤ ∫ x, β x * M :=
    norm_integral_le_of_norm_le ((β.integrable (μ := volume)).mul_const M)
    (Filter.Eventually.of_forall hpoint)
  rw [integral_mul_const] at hnorm
  have hmass : (∫ x, β x) ≤ 2 * r := by
    calc
      (∫ x, β x) ≤ volume.real (closedBall a β.rOut) := β.integral_le_measure_closedBall volume
      _ = 2 * r := by rw [Real.volume_real_closedBall β.rOut_pos.le, hβr]
  exact hnorm.trans ((mul_le_mul_of_nonneg_right hmass hM).trans_eq (by ring))

theorem slowdownVectorMoment_norm_le {m : ℕ} {f : ℝ → EuclideanSpace ℝ (Fin m)}
    {L a r M : ℝ} (hr : 0 < r) (b : ℝ → ℝ) (hM : 0 ≤ M)
    (hbound : ∀ x ∈ Icc 0 L, ‖b x • f x‖ ≤ M)
    (hleft : 0 ≤ a - r) (hright : a + r ≤ L) :
    ‖slowdownVectorMoment L a r hr b f‖ ≤ 2 * M * r := by
  rw [slowdownVectorMoment, controlMoment_interval_eq_real
    (slowdownControl_support hr b hleft hright)]
  apply norm_slowdown_real_moment_le hr b hM
  intro x hx
  rw [Real.closedBall_eq_Icc] at hx
  exact hbound x ⟨hleft.trans hx.1, hx.2.trans hright⟩

theorem exists_positive_baseline_moment_bound {m : ℕ} {f : ℝ → EuclideanSpace ℝ (Fin m)}
    (hf : Continuous f) {b : ℝ → ℝ} (hb : Continuous b) (L : ℝ) :
    ∃ M : ℝ, 0 < M ∧ ∀ x ∈ Icc 0 L, ‖b x • f x‖ ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hb.smul hf).continuousOn
  refine ⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x hx
  exact (hM x hx).trans (le_max_left _ _)

theorem slowdown_coefficients_l1_le {m n : ℕ} {f : ℝ → EuclideanSpace ℝ (Fin m)}
    {L a r M C : ℝ} (hr : 0 < r) (b : ℝ → ℝ) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hbound : ∀ x ∈ Icc 0 L, ‖b x • f x‖ ≤ M)
    (hleft : 0 ≤ a - r) (hright : a + r ≤ L)
    (T : momentSampleSpan f (Ioo 0 L) → Fin n → ℝ)
    (hT : ∀ u : momentSampleSpan f (Ioo 0 L), (∑ j, |T u j|) ≤ C * ‖u‖)
    (u : momentSampleSpan f (Ioo 0 L))
    (hu : (u : EuclideanSpace ℝ (Fin m)) = slowdownVectorMoment L a r hr b f) :
    (∑ j, |T u j|) ≤ 2 * C * M * r := by
  have huBound : ‖u‖ ≤ 2 * M * r := by
    change ‖(u : EuclideanSpace ℝ (Fin m))‖ ≤ _
    rw [hu]
    exact slowdownVectorMoment_norm_le hr b hM hbound hleft hright
  exact (hT u).trans ((mul_le_mul_of_nonneg_left huBound hC).trans_eq (by ring))

end
end TightVer401
