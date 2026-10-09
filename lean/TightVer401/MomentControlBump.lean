import Mathlib

namespace TightVer401
noncomputable section
open Set Filter MeasureTheory Metric
open scoped ContDiff Topology

def momentControlBump (c r : ℝ) (hr : 0 < r) : ContDiffBump c :=
  { rIn := r / 2, rOut := r, rIn_pos := half_pos hr, rIn_lt_rOut := half_lt_self hr }

def normalizedMomentControl (c r : ℝ) (hr : 0 < r) : ℝ → ℝ :=
  (momentControlBump c r hr).normed volume

theorem normalizedMomentControl_contDiff (c r : ℝ) (hr : 0 < r) :
    ContDiff ℝ ∞ (normalizedMomentControl c r hr) :=
  (momentControlBump c r hr).contDiff_normed

theorem normalizedMomentControl_nonneg (c r : ℝ) (hr : 0 < r) (x : ℝ) :
    0 ≤ normalizedMomentControl c r hr x :=
  (momentControlBump c r hr).nonneg_normed x

theorem normalizedMomentControl_integral (c r : ℝ) (hr : 0 < r) :
    ∫ x : ℝ, normalizedMomentControl c r hr x = 1 :=
  (momentControlBump c r hr).integral_normed

theorem normalizedMomentControl_support (c r : ℝ) (hr : 0 < r) :
    Function.support (normalizedMomentControl c r hr) = Ioo (c - r) (c + r) := by
  rw [normalizedMomentControl, (momentControlBump c r hr).support_normed_eq,
    Real.ball_eq_Ioo]
  rfl

theorem normalizedMomentControl_tsupport (c r : ℝ) (hr : 0 < r) :
    tsupport (normalizedMomentControl c r hr) = Icc (c - r) (c + r) := by
  rw [normalizedMomentControl, (momentControlBump c r hr).tsupport_normed_eq,
    Real.closedBall_eq_Icc]
  rfl

def realControlMoment {m : ℕ} (f : ℝ → EuclideanSpace ℝ (Fin m)) (ψ : ℝ → ℝ) :=
  ∫ x : ℝ, ψ x • f x

theorem normedBump_moment_integrable {m : ℕ} {f : ℝ → EuclideanSpace ℝ (Fin m)}
    (hf : Continuous f) {c : ℝ} (b : ContDiffBump c) :
    Integrable (fun x => b.normed volume x • f x) :=
  (b.continuous_normed.smul hf).integrable_of_hasCompactSupport b.hasCompactSupport_normed.smul_right

theorem normedBump_moment_error_le {m : ℕ} {f : ℝ → EuclideanSpace ℝ (Fin m)}
    (hf : Continuous f) {c : ℝ} (b : ContDiffBump c) {ε : ℝ} (_hε : 0 ≤ ε)
    (hclose : ∀ x ∈ ball c b.rOut, ‖f x - f c‖ ≤ ε) :
    ‖realControlMoment f (b.normed volume) - f c‖ ≤ ε := by
  have hbf := normedBump_moment_integrable hf b
  have hbc : Integrable (fun x => b.normed volume x • f c) :=
    b.integrable_normed.smul_const _
  have hbound : ∀ x : ℝ,
      ‖b.normed volume x • f x - b.normed volume x • f c‖ ≤ b.normed volume x * ε := by
    intro x
    by_cases hx : x ∈ ball c b.rOut
    · rw [← smul_sub, norm_smul, Real.norm_of_nonneg (b.nonneg_normed x)]
      exact mul_le_mul_of_nonneg_left (hclose x hx) (b.nonneg_normed x)
    · have hx0 : b.normed volume x = 0 := by
        apply Function.notMem_support.mp
        rwa [b.support_normed_eq]
      simp [hx0]
  have hnorm := norm_integral_le_of_norm_le (b.integrable_normed.mul_const ε)
    (Filter.Eventually.of_forall hbound)
  rw [integral_sub hbf hbc, b.integral_normed_smul volume (f c), integral_mul_const,
    b.integral_normed, one_mul] at hnorm
  exact hnorm

theorem normedBump_moment_tendsto {m : ℕ} {f : ℝ → EuclideanSpace ℝ (Fin m)}
    (hf : Continuous f) {c : ℝ} {ι : Type*} {l : Filter ι} {b : ι → ContDiffBump c}
    (hr : Tendsto (fun i => (b i).rOut) l (𝓝 0)) :
    Tendsto (fun i => realControlMoment f ((b i).normed volume)) l (𝓝 (f c)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨δ, hδ, hfδ⟩ := Metric.eventually_nhds_iff.mp
    (hf.continuousAt.eventually (Metric.ball_mem_nhds (f c) hε2))
  have hrδ : ∀ᶠ i in l, (b i).rOut < δ := hr.eventually (gt_mem_nhds hδ)
  filter_upwards [hrδ] with i hi
  have hbclose : ∀ x ∈ ball c (b i).rOut, ‖f x - f c‖ ≤ ε / 2 := by
    intro x hx
    have hfx := hfδ (hx.trans hi)
    exact (by simpa only [mem_ball, dist_eq_norm] using hfx : ‖f x - f c‖ < ε / 2).le
  have hle := normedBump_moment_error_le hf (b i) hε2.le hbclose
  rw [dist_eq_norm]
  exact hle.trans_lt (half_lt_self hε)

theorem normalizedMomentControl_intervalMoment {m : ℕ} (f : ℝ → EuclideanSpace ℝ (Fin m))
    (c r L : ℝ) (hr : 0 < r) (hleft : 0 ≤ c - r) (hright : c + r ≤ L) :
    (∫ x in 0..L, normalizedMomentControl c r hr x • f x) =
      realControlMoment f (normalizedMomentControl c r hr) := by
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro x hx
  have hxψ : x ∈ Function.support (normalizedMomentControl c r hr) := by
    contrapose! hx
    simp only [Function.mem_support, not_not] at hx ⊢
    simp [hx]
  rw [normalizedMomentControl_support] at hxψ
  exact ⟨hleft.trans_lt hxψ.1, hxψ.2.le.trans hright⟩

end
end TightVer401
