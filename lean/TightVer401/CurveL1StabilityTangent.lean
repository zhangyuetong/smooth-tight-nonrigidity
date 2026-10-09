import OAI.Geometry.SurfaceImmersion.Primitive.PeriodicPrimitive

namespace TightVer401
noncomputable section
open Set Metric OAI.ClosedSurfaceR4.PeriodicPrimitive

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A common positive projection direction near each point in a whole period.
Its neighborhood size depends only on the actual continuous nonzero tangent. -/
theorem exists_speedCurve_tangent_radius {L : ℝ} (hL : 0 < L) (P : ℝ → E)
    (hP : Continuous P) (hne : ∀ x, P x ≠ 0) :
    ∃ δ > 0, δ < L ∧ ∀ x ∈ Icc 0 L, ∀ y : ℝ,
      |y - x| < δ → 0 < inner ℝ (P x) (P y) := by
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨0, ⟨le_rfl, hL.le⟩⟩
    hP.norm.continuousOn
  let μ := ‖P x₀‖
  have hμ : 0 < μ := norm_pos_iff.mpr (hne x₀)
  have hμbound (x) (hx : x ∈ Icc 0 L) : μ ≤ ‖P x‖ := hmin hx
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hP.continuousOn
    (s := Icc (-L) (2 * L))
  obtain ⟨d, hd, hclose⟩ := Metric.uniformContinuousOn_iff.mp huc (μ / 2) (half_pos hμ)
  obtain ⟨δ, hδ, hδmin⟩ := exists_between (lt_min hd hL)
  have hδd : δ < d := hδmin.trans_le (min_le_left _ _)
  have hδL : δ < L := hδmin.trans_le (min_le_right _ _)
  refine ⟨δ, hδ, hδL, ?_⟩
  intro x hx y hy
  have hxy := abs_lt.mp hy
  have hxK : x ∈ Icc (-L) (2 * L) := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hyK : y ∈ Icc (-L) (2 * L) := ⟨by linarith [hx.1, hxy.1], by linarith [hx.2, hxy.2]⟩
  have hdist : dist x y < d := by rw [Real.dist_eq, abs_sub_comm]; exact hy.trans hδd
  have hdiff : ‖P y - P x‖ < μ / 2 := by
    simpa only [dist_eq_norm, norm_sub_rev] using hclose x hxK y hyK hdist
  have hPx : 0 < ‖P x‖ := norm_pos_iff.mpr (hne x)
  have hsmall : ‖P y - P x‖ < ‖P x‖ := by linarith [hμbound x hx]
  have hcauchy := neg_le_of_abs_le (abs_real_inner_le_norm (P x) (P y - P x))
  have he := inner_sub_right (𝕜 := ℝ) (P x) (P y) (P x)
  rw [real_inner_self_eq_norm_sq] at he
  have hp := mul_pos hPx (sub_pos.mpr hsmall)
  nlinarith

end
end TightVer401
