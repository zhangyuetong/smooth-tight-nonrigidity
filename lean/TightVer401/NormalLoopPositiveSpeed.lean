import TightVer401.NormalLoopMomentInterior

namespace TightVer401
noncomputable section
open Set Filter MeasureTheory Metric
open scoped ContDiff Topology Manifold BigOperators

theorem exists_positive_periodic_closing_speed_of_moment_interior {m : ℕ} (L : ℝ)
    {f : ℝ → EuclideanSpace ℝ (Fin m)} (hf : Continuous f)
    (h0 : (0 : EuclideanSpace ℝ (Fin m)) ∈
      interior (nonnegativeSmoothPeriodMoments L f)) :
    ∃ b : ℝ → ℝ, ContDiff ℝ ∞ b ∧ Function.Periodic b L ∧
      (∀ s, 0 < b s) ∧ momentPathMoment L f b = 0 := by
  let M := momentPathMoment L f (fun _ => 1)
  have hT : Tendsto (fun k => -(momentControlRadius k) • M) atTop (𝓝 0) := by
    simpa only [neg_zero, zero_smul] using momentControlRadius_tendsto.neg.smul_const M
  have he := hT.eventually (mem_interior_iff_mem_nhds.mp h0)
  obtain ⟨k, hk⟩ := he.exists
  obtain ⟨a, ha, hpa, hna, hmoment⟩ := hk
  let δ := momentControlRadius k
  refine ⟨fun s => δ + a s, contDiff_const.add ha, ?_, ?_, ?_⟩
  · intro s
    simp only [hpa s]
  · intro s
    exact add_pos_of_pos_of_nonneg (momentControlRadius_pos k) (hna s)
  · have hiδ : IntervalIntegrable (fun s => δ • f s) volume 0 L :=
      ((continuous_const (y := δ)).smul hf).intervalIntegrable 0 L
    have hia : IntervalIntegrable (fun s => a s • f s) volume 0 L :=
      (ha.continuous.smul hf).intervalIntegrable 0 L
    unfold momentPathMoment
    simp_rw [add_smul]
    rw [intervalIntegral.integral_add hiδ hia, intervalIntegral.integral_smul]
    have hM : M = ∫ s in 0..L, f s := by simp [M, momentPathMoment]
    rw [← hM]
    change δ • M + momentPathMoment L f a = 0
    rw [hmoment]
    simp only [δ, neg_smul, add_neg_cancel]

theorem exists_positive_periodic_closing_speed_of_origin_interior {m : ℕ} (L : ℝ)
    [Fact (0 < L)] {f : AddCircle L → EuclideanSpace ℝ (Fin m)}
    (hf : Continuous f) (hg : ContDiff ℝ ∞ (f ∘ periodProjection L))
    (h0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ interior (convexHull ℝ (Set.range f))) :
    ∃ b : ℝ → ℝ, ContDiff ℝ ∞ b ∧ Function.Periodic b L ∧
      (∀ s, 0 < b s) ∧ momentPathMoment L (f ∘ periodProjection L) b = 0 :=
  exists_positive_periodic_closing_speed_of_moment_interior L hg.continuous
    (origin_interior_nonnegativeSmoothPeriodMoments L hf hg h0)

theorem exists_positive_circle_closing_speed_of_origin_interior {m : ℕ} (L : ℝ)
    [Fact (0 < L)] {f : AddCircle L → EuclideanSpace ℝ (Fin m)}
    (hf : Continuous f) (hg : ContDiff ℝ ∞ (f ∘ periodProjection L))
    (h0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ interior (convexHull ℝ (Set.range f))) :
    letI := periodCircleChartedSpace L
    ∃ b : AddCircle L → ℝ, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ b ∧
      (∀ q, 0 < b q) ∧ circleControlMoment L f b = 0 := by
  letI := periodCircleChartedSpace L
  obtain ⟨a, ha, hpa, hpos, hm⟩ :=
    exists_positive_periodic_closing_speed_of_origin_interior L hf hg h0
  refine ⟨hpa.lift, periodicLift_contMDiff ha hpa, ?_, ?_⟩
  · intro q
    obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective q
    rw [hpa.lift_coe]
    exact hpos s
  · simpa only [circleControlMoment, momentPathMoment, Function.comp_apply, periodicLift_coe] using hm

end
end TightVer401
