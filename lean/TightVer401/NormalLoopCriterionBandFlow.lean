import TightVer401.NormalLoopCriterionBand

namespace TightVer401
noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

theorem periodicRuledFrame_positive_flow_stays_in_band {T : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T) (s w : ℝ) (hw : 0 < w) :
    ∃ δ > 0, ∀ v : ℝ, 0 < v → v < δ → ∀ t ∈ Icc s (s + T),
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) s v t ∈ Ioo 0 w := by
  let ρ := ruledRho d.τ
  let W := ruledOmega d.k d.τ
  have hρpos (t) : 0 < ρ t := ruledRho_pos (d.torsion_ne_zero t)
  have hW : Continuous W := continuous_iff_continuousAt.mpr
    (fun t => (ruledOmega_hasDerivAt d.smooth_k d.smooth_τ d.torsion_ne_zero t).continuousAt)
  obtain ⟨μ, hμ, hμρ⟩ := momentSlowdown_periodic_min T
    (ruledRho_contDiff d.smooth_τ d.torsion_ne_zero) (ruledRho_periodic d.period_τ) hρpos
  obtain ⟨δ₀, hδ₀, hden⟩ := principalTrajectory_uniform_denominator
    (ρ := ρ) (s := s) isCompact_Icc hW.continuousOn
  let δ := min δ₀ (w * μ / (2 * ρ s))
  have hδ : 0 < δ := lt_min hδ₀ (div_pos (mul_pos hw hμ) (mul_pos (by norm_num) (hρpos s)))
  refine ⟨δ, hδ, fun v hv hvδ t ht => ?_⟩
  have hv₀ : |v| < δ₀ := by
    simpa only [abs_of_pos hv] using hvδ.trans_le (min_le_left δ₀ (w * μ / (2 * ρ s)))
  have hden₀ := hden v hv₀ t ht
  have hD : μ / 2 < ρ t * (1 + ρ s * v * (W t - W s)) := by
    calc
      μ / 2 = μ * (1 / 2) := by ring
      _ ≤ ρ t * (1 / 2) := mul_le_mul_of_nonneg_right (hμρ t) (by norm_num)
      _ < ρ t * (1 + ρ s * v * (W t - W s)) :=
        mul_lt_mul_of_pos_left hden₀ (hρpos t)
  have hDpos : 0 < ρ t * (1 + ρ s * v * (W t - W s)) := (half_pos hμ).trans hD
  have hvbound : v < w * μ / (2 * ρ s) := hvδ.trans_le (min_le_right _ _)
  have hnum : ρ s * v < w * μ / 2 := by
    have h := (lt_div_iff₀ (mul_pos (by norm_num) (hρpos s))).mp hvbound
    nlinarith
  change 0 < (ρ s * v) / (ρ t * (1 + ρ s * v * (W t - W s))) ∧
    (ρ s * v) / (ρ t * (1 + ρ s * v * (W t - W s))) < w
  refine ⟨div_pos (mul_pos (hρpos s) hv) hDpos, (div_lt_iff₀ hDpos).mpr ?_⟩
  have h := mul_lt_mul_of_pos_left hD hw
  nlinarith

theorem periodicRuledFrame_identity_flow_inside_band {T : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T)
    (hgeometry : PrincipalNormalIdentityBand d)
    (s w : ℝ) (hw : 0 < w) :
    ∃ δ > 0, δ < w ∧ ∀ v : ℝ, 0 < v → v < δ →
      let U := principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) s v
      U s = v ∧ (∀ t ∈ Icc s (s + T), U t ∈ Ioo 0 w) ∧
      (∀ t ∈ Icc s (s + T), HasDerivAt U
        (-(U t / 2) * (ruledLambda d.τ t + U t * ruledD d.k d.τ t)) t) ∧
      (∀ t ∈ Icc s (s + T),
        let p : OAI.SmoothLocal.Geometry.Coord := ![t, U t]
        let tangent := deriv (fun r => (![r, U r] : OAI.SmoothLocal.Geometry.Coord)) t
        dotProduct tangent
          ((OAI.SmoothLocal.Geometry.secondFundamental (ruledMap d.γ d.E)
            (ruledNormal (d.T t) (d.n t) (d.k t) (d.τ t) (U t)) p).mulVec tangent) = 0) ∧
      U (s + T) = v := by
  obtain ⟨δ₀, hδ₀, hinside⟩ := periodicRuledFrame_positive_flow_stays_in_band d s w hw
  obtain ⟨δ₁, hδ₁, hidentity⟩ := hgeometry.2.2.2.2 s
  let δ := min (w / 2) (min δ₀ δ₁)
  have hδ : 0 < δ := lt_min (half_pos hw) (lt_min hδ₀ hδ₁)
  have hδw : δ < w := (min_le_left _ _).trans_lt (half_lt_self hw)
  have hδ₀bound : δ ≤ δ₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hδ₁bound : δ ≤ δ₁ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ, hδ, hδw, fun v hv hvδ => ?_⟩
  have hv₁ : |v| < δ₁ := by simpa only [abs_of_pos hv] using hvδ.trans_le hδ₁bound
  obtain ⟨hinit, hderiv, hasym, hreturn⟩ := hidentity v hv₁
  exact ⟨hinit, hinside v hv (hvδ.trans_le hδ₀bound), hderiv, hasym, hreturn⟩

end
end TightVer401
