import TightVer401.NormalLoopCriterionBandFlow

namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.SmoothLocal.Geometry
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

/-- Zero actual period integral makes the actual primitive periodic. -/
theorem periodicRuledFrame_omega_periodic {T : ℝ} (d : PeriodicRuledFrame T)
    (hbalance : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0) :
    Function.Periodic (ruledOmega d.k d.τ) T := by
  intro t
  have h := ruledOmega_increment d.smooth_k d.smooth_τ d.torsion_ne_zero
    d.period_k d.period_τ t
  rw [hbalance] at h
  exact sub_eq_zero.mp h

theorem principalTrajectory_periodic {ρ W : ℝ → ℝ} {T : ℝ}
    (hρ : Function.Periodic ρ T) (hW : Function.Periodic W T) (s v : ℝ) :
    Function.Periodic (principalTrajectory ρ W s v) T := by
  intro t
  simp only [principalTrajectory, hρ t, hW t]

/-- The denominator is controlled on all of the real line, using the compact
period circle rather than a single traversal interval. -/
theorem periodicRuledFrame_global_denominator {T : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T)
    (hbalance : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0) (s : ℝ) :
    ∃ δ > 0, ∀ v : ℝ, |v| < δ → ∀ t : ℝ,
      1 / 2 < 1 + ruledRho d.τ s * v * (ruledOmega d.k d.τ t - ruledOmega d.k d.τ s) := by
  let W := ruledOmega d.k d.τ
  have hW : ContDiff ℝ ∞ W :=
    OAI.ClosedSurfaceR4.PeriodicPrimitive.rawPrimitive_contDiff
      (ruledPeriodCoefficient_contDiff d.smooth_k d.smooth_τ d.torsion_ne_zero)
  have hWL : Function.Periodic W T := periodicRuledFrame_omega_periodic d hbalance
  let F := fun t => ruledRho d.τ s * (W t - W s)
  have hF : ContDiff ℝ ∞ F := contDiff_const.mul (hW.sub contDiff_const)
  have hFL : Function.Periodic F T := by intro t; simp only [F, hWL t]
  obtain ⟨B, hB, hb⟩ := momentSlowdown_periodic_bound T hF hFL
  refine ⟨1 / (2 * B), one_div_pos.mpr (mul_pos (by norm_num) hB), ?_⟩
  intro v hv t
  have hm := mul_lt_mul_of_pos_right hv hB
  have he : (1 / (2 * B)) * B = 1 / 2 := by field_simp
  rw [he] at hm
  have hp : |ruledRho d.τ s * v * (W t - W s)| < 1 / 2 := by
    calc
      |ruledRho d.τ s * v * (W t - W s)| = |v| * |F t| := by
        rw [← abs_mul]; congr 1; dsimp [F]; ring
      _ ≤ |v| * B := mul_le_mul_of_nonneg_left (hb t) (abs_nonneg _)
      _ < 1 / 2 := hm
  have hn := (abs_lt.mp hp).1
  change 1 / 2 < 1 + ruledRho d.τ s * v * (W t - W s)
  linarith

/-- A common positive initial interval produces complete periodic asymptotic
leaves, each entirely contained in the requested positive band. -/
theorem periodicRuledFrame_closed_asymptotic_leaves {T : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T)
    (hbalance : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0)
    (s w : ℝ) (hw : 0 < w) :
    ∃ δ > 0, δ < w ∧ ∀ v : ℝ, 0 < v → v < δ →
      let U := principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) s v
      U s = v ∧ Function.Periodic U T ∧ ContDiff ℝ ∞ U ∧
      (∀ t : ℝ, U t ∈ Ioo 0 w) ∧
      (∀ t : ℝ, HasDerivAt U
        (-(U t / 2) * (ruledLambda d.τ t + U t * ruledD d.k d.τ t)) t) ∧
      (∀ t : ℝ,
        let p : Coord := ![t, U t]
        let tangent := deriv (fun r => (![r, U r] : Coord)) t
        dotProduct tangent
          ((secondFundamental (ruledMap d.γ d.E)
            (ruledNormal (d.T t) (d.n t) (d.k t) (d.τ t) (U t)) p).mulVec tangent) = 0) := by
  let ρ := ruledRho d.τ
  let W := ruledOmega d.k d.τ
  have hρpos (t) : 0 < ρ t := ruledRho_pos (d.torsion_ne_zero t)
  have hρ : ContDiff ℝ ∞ ρ := ruledRho_contDiff d.smooth_τ d.torsion_ne_zero
  have hW : ContDiff ℝ ∞ W :=
    OAI.ClosedSurfaceR4.PeriodicPrimitive.rawPrimitive_contDiff
      (ruledPeriodCoefficient_contDiff d.smooth_k d.smooth_τ d.torsion_ne_zero)
  obtain ⟨μ, hμ, hμρ⟩ := momentSlowdown_periodic_min T hρ
    (ruledRho_periodic d.period_τ) hρpos
  obtain ⟨δ₀, hδ₀, hden⟩ := periodicRuledFrame_global_denominator d hbalance s
  let δ := min (w / 2) (min δ₀ (w * μ / (2 * ρ s)))
  have hδ : 0 < δ := lt_min (half_pos hw) (lt_min hδ₀
    (div_pos (mul_pos hw hμ) (mul_pos (by norm_num) (hρpos s))))
  refine ⟨δ, hδ, (min_le_left _ _).trans_lt (half_lt_self hw), ?_⟩
  intro v hv hvδ
  let U := principalTrajectory ρ W s v
  have hv₀ : |v| < δ₀ := by
    simpa only [abs_of_pos hv] using hvδ.trans_le
      ((min_le_right _ _).trans (min_le_left _ _))
  have hdenpos (t) : 0 < 1 + ρ s * v * (W t - W s) := by
    exact (show (0 : ℝ) < 1 / 2 by norm_num).trans (hden v hv₀ t)
  have hD (t) : μ / 2 < ρ t * (1 + ρ s * v * (W t - W s)) := by
    calc
      μ / 2 = μ * (1 / 2) := by ring
      _ ≤ ρ t * (1 / 2) := mul_le_mul_of_nonneg_right (hμρ t) (by norm_num)
      _ < ρ t * (1 + ρ s * v * (W t - W s)) :=
        mul_lt_mul_of_pos_left (hden v hv₀ t) (hρpos t)
  have hDpos (t) := mul_pos (hρpos t) (hdenpos t)
  have hu : ContDiff ℝ ∞ U := contDiff_const.div
    (hρ.mul (contDiff_const.add (contDiff_const.mul (hW.sub contDiff_const))))
    (fun t => ne_of_gt (hDpos t))
  have hderiv (t) : HasDerivAt U
      (-(U t / 2) * (ruledLambda d.τ t + U t * ruledD d.k d.τ t)) t :=
    principalTrajectory_hasDerivAt
      (ruledRho_hasDerivAt (d.smooth_τ.differentiable (by simp) t).hasDerivAt
        (d.torsion_ne_zero t))
      (ruledOmega_hasDerivAt d.smooth_k d.smooth_τ d.torsion_ne_zero t)
      (ne_of_gt (hρpos t)) (ne_of_gt (hdenpos t))
  refine ⟨principalTrajectory_initial (ne_of_gt (hρpos s)),
    principalTrajectory_periodic (ruledRho_periodic d.period_τ)
      (periodicRuledFrame_omega_periodic d hbalance) s v, hu, ?_, hderiv, ?_⟩
  · intro t
    have hvbound : v < w * μ / (2 * ρ s) := hvδ.trans_le
      ((min_le_right _ _).trans (min_le_right _ _))
    have hnum : ρ s * v < w * μ / 2 := by
      have h := (lt_div_iff₀ (mul_pos (by norm_num) (hρpos s))).mp hvbound
      nlinarith
    change 0 < (ρ s * v) / (ρ t * (1 + ρ s * v * (W t - W s))) ∧
      (ρ s * v) / (ρ t * (1 + ρ s * v * (W t - W s))) < w
    refine ⟨div_pos (mul_pos (hρpos s) hv) (hDpos t),
      (div_lt_iff₀ (hDpos t)).mpr ?_⟩
    have h := mul_lt_mul_of_pos_left (hD t) hw
    nlinarith
  · intro t
    rw [(ruled_graph_hasDerivAt (hderiv t)).deriv]
    have hX := (periodicRuledFrame_identity_band d hbalance).1
    apply (ruled_asymptotic_slope d.deriv_γ d.deriv_E (d.deriv_T t) (d.deriv_n t)
      (d.smooth_k.differentiable (by simp) t).hasDerivAt
      (d.smooth_τ.differentiable (by simp) t).hasDerivAt
      hX.contDiffOn isOpen_univ (mem_univ _) (d.orthonormal t)
      (d.torsion_ne_zero t)).mpr
    rfl

end
end TightVer401
