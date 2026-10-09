import TightVer401.GeneralRuledPeriodic

/-! The appendix return proposition, assembled from actual differential
geometry, constructed characteristic flows and their proved uniqueness. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

theorem general_ruled_return {c e : ℝ → Ambient} {L : ℝ}
    (hc : ContDiff ℝ ∞ c) (he : ContDiff ℝ ∞ e)
    (hcL : Function.Periodic c L) (heL : Function.Periodic e L) (hL : 0 < L)
    (hdet : ∀ s, Matrix.det ![fun i => deriv c s i, fun i => e s i,
      fun i => deriv e s i] ≠ 0)
    (hcentral : ∀ s, secondFundamental (ruledMap c e)
      (generalRuledNormal (deriv c) e (deriv e) (![s, 0] : Coord)) (![s, 0] : Coord) 0 0 = 0) :
    (∀ t u, ruledMap c e (![t + L, u] : Coord) = ruledMap c e (![t, u] : Coord)) ∧
    (Function.Periodic (generalRuledLinearCoefficient c e) L ∧
      Function.Periodic (generalRuledQuadraticCoefficient c e) L) ∧
    (∀ p : Coord, gaussianCurvature (inducedMetric (ruledMap c e)) p =
      -(generalRuledDelta (deriv c) e (deriv e) (p 0))^2 /
        ‖generalRuledCross (deriv c) e (deriv e) p‖^4 ∧
      gaussianCurvature (inducedMetric (ruledMap c e)) p < 0) ∧
    (∀ (p : Coord) (w : ℝ),
      dotProduct (![1, w] : Coord)
        ((secondFundamental (ruledMap c e) (generalRuledNormal (deriv c) e (deriv e) p) p).mulVec ![1, w]) = 0 ↔
        w = generalRuledLinearCoefficient c e (p 0) * p 1 +
          generalRuledQuadraticCoefficient c e (p 0) * (p 1)^2) ∧
    (∃ δ > 0, ∀ u : ℝ → ℝ, |u 0| < δ →
      (∀ t ∈ Icc 0 L, HasDerivAt u (deriv u t) t) →
      (∀ t ∈ Icc 0 L,
        let p : Coord := ![t, u t]
        let v : Coord := deriv (fun r => (![r, u r] : Coord)) t
        dotProduct v ((secondFundamental (ruledMap c e)
          (generalRuledNormal (deriv c) e (deriv e) p) p).mulVec v) = 0) →
      u L = generalRuledReturn c e L (u 0)) ∧
    ((generalRuledReturn c e L =ᶠ[𝓝 0] (fun u => u)) ↔
      Real.exp (riccatiA (generalRuledLinearCoefficient c e) L) = 1 ∧
        riccatiV (generalRuledLinearCoefficient c e) (generalRuledQuadraticCoefficient c e) L = 0) ∧
    ((generalRuledReturn c e L =ᶠ[𝓝 0] (fun u => u)) ↔
      deriv (generalRuledReturn c e L) 0 = 1 ∧ deriv (deriv (generalRuledReturn c e L)) 0 = 0) := by
  have hδ : ∀ s, generalRuledDelta (deriv c) e (deriv e) s ≠ 0 := by
    intro s
    rw [generalRuledDelta_eq_det]
    exact hdet s
  refine ⟨general_ruled_periodic_map hcL heL, general_ruled_periodic_coefficients hcL heL,
    ?_, general_ruled_actual_riccati hc he hδ hcentral,
    general_ruled_return_of_asymptotic_curve hc he hδ hcentral hL.le,
    (general_ruled_return_identity_iff c e L).1, (general_ruled_return_identity_iff c e L).2⟩
  intro p
  have hK := general_ruled_gaussianCurvature hc he hδ p
  refine ⟨hK, ?_⟩
  rw [hK]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (sq_pos_of_ne_zero (hδ (p 0))))
    (pow_pos (norm_pos_iff.mpr (general_ruled_cross_ne_zero (hδ (p 0)))) 4)

end
end TightVer401
