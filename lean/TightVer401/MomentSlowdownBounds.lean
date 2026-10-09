import TightVer401.MomentControlCoefficients
import TightVer401.MomentPeriodicControl

namespace TightVer401
noncomputable section
open Set Filter MeasureTheory Metric
open scoped ContDiff Topology Manifold BigOperators

theorem momentSlowdown_periodic_min (L : ℝ) [Fact (0 < L)] {b : ℝ → ℝ}
    (hb : ContDiff ℝ ∞ b) (hperiod : Function.Periodic b L) (hpos : ∀ s, 0 < b s) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ s, μ ≤ b s := by
  letI := periodCircleChartedSpace L
  have hc : Continuous hperiod.lift := (periodicLift_contMDiff hb hperiod).continuous
  obtain ⟨q, _, hq⟩ := isCompact_univ.exists_isMinOn (univ_nonempty) hc.continuousOn
  obtain ⟨s, hs⟩ := QuotientAddGroup.mk_surjective q
  refine ⟨b s, hpos s, fun t => ?_⟩
  have ht := hq (mem_univ (periodProjection L t))
  change hperiod.lift q ≤ hperiod.lift (periodProjection L t) at ht
  rw [← hs, hperiod.lift_coe, periodicLift_coe] at ht
  exact ht

theorem momentSlowdown_periodic_bound (L : ℝ) [Fact (0 < L)] {b : ℝ → ℝ}
    (hb : ContDiff ℝ ∞ b) (hperiod : Function.Periodic b L) :
    ∃ M : ℝ, 0 < M ∧ ∀ s, |b s| ≤ M := by
  letI := periodCircleChartedSpace L
  have hc : Continuous hperiod.lift := (periodicLift_contMDiff hb hperiod).continuous
  obtain ⟨q, _, hq⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hc.abs.continuousOn
  refine ⟨|hperiod.lift q| + 1, by positivity, fun s => ?_⟩
  have hs := hq (mem_univ (periodProjection L s))
  change |hperiod.lift (periodProjection L s)| ≤ |hperiod.lift q| at hs
  rw [periodicLift_coe] at hs
  linarith

theorem momentSlowdown_control_bound {n : ℕ} (L : ℝ) [Fact (0 < L)]
    {ψ : Fin n → ℝ → ℝ} (hψ : ∀ j, ContDiff ℝ ∞ (ψ j))
    (hperiod : ∀ j, Function.Periodic (ψ j) L) :
    ∃ K : ℝ, 0 < K ∧ ∀ j s, |ψ j s| ≤ K := by
  choose M hM hbound using fun j => momentSlowdown_periodic_bound L (hψ j) (hperiod j)
  let K := (∑ j, M j) + 1
  have hsum : 0 ≤ ∑ j, M j := Finset.sum_nonneg (fun j _ => (hM j).le)
  refine ⟨K, by dsimp [K]; linarith, fun j s => ?_⟩
  have hj : M j ≤ ∑ i, M i := Finset.single_le_sum (fun i _ => (hM i).le) (Finset.mem_univ j)
  dsimp [K]
  linarith [hbound j s]

theorem momentSlowdown_bump_support {a r : ℝ} (hr : 0 < r) :
    Function.support (momentControlBump a r hr : ℝ → ℝ) = Ioo (a - r) (a + r) := by
  rw [(momentControlBump a r hr).support_eq, Real.ball_eq_Ioo]
  rfl

theorem momentSlowdown_bump_tsupport {a r : ℝ} (hr : 0 < r) :
    tsupport (momentControlBump a r hr : ℝ → ℝ) = Icc (a - r) (a + r) := by
  rw [(momentControlBump a r hr).tsupport_eq, Real.closedBall_eq_Icc]
  rfl

theorem momentSlowdown_bump_plateau {a r : ℝ} (hr : 0 < r) {s : ℝ}
    (hs : s ∈ Icc (a - r / 2) (a + r / 2)) : momentControlBump a r hr s = 1 := by
  apply (momentControlBump a r hr).one_of_mem_closedBall
  simpa only [Real.closedBall_eq_Icc, momentControlBump] using hs

theorem momentSlowdown_bump_integral_norm_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {a r M : ℝ} (hr : 0 < r)
    (F : ℝ → E) (hbound : ∀ s ∈ Icc (a - r) (a + r), ‖F s‖ ≤ M) :
    ‖∫ s : ℝ, momentControlBump a r hr s • F s‖ ≤ 2 * r * M := by
  have he : (∫ s in (a - r)..(a + r), momentControlBump a r hr s • F s) =
      ∫ s : ℝ, momentControlBump a r hr s • F s := by
    apply intervalIntegral.integral_eq_integral_of_support_subset
    intro s hs
    have hb : momentControlBump a r hr s ≠ 0 := by
      intro hz
      exact hs (by simp [hz])
    have hball : s ∈ Ioo (a - r) (a + r) := by
      rw [← momentSlowdown_bump_support hr]
      exact hb
    exact Ioo_subset_Ioc_self hball
  rw [← he]
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a - r) (b := a + r) (f := fun s => momentControlBump a r hr s • F s)
    (C := M) (fun s hs => by
      rw [uIoc_of_le (by linarith : a - r ≤ a + r)] at hs
      rw [norm_smul, Real.norm_of_nonneg (momentControlBump a r hr).nonneg]
      calc
        momentControlBump a r hr s * ‖F s‖ ≤ 1 * ‖F s‖ :=
          mul_le_mul_of_nonneg_right (momentControlBump a r hr).le_one (norm_nonneg _)
        _ ≤ M := by simpa only [one_mul] using hbound s (Ioc_subset_Icc_self hs))
  have hlength : |(a + r) - (a - r)| = 2 * r := by
    rw [abs_of_pos (by linarith)]
    ring
  rw [hlength] at hnorm
  nlinarith [hnorm]

end
end TightVer401
