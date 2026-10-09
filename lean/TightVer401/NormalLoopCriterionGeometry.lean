import TightVer401.NormalLoopPrescription
import TightVer401.RuledFlow

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

/-- Actual coordinate immersion, intrinsic curvature, and a constructed identity
return flow of the nonruling asymptotic family. -/
def PrincipalNormalIdentityBand {T : ℝ} (d : PeriodicRuledFrame T) : Prop :=
  ContDiff ℝ ∞ (ruledMap d.γ d.E) ∧
  (∀ s u, ruledMap d.γ d.E (![s + T, u] : Coord) = ruledMap d.γ d.E (![s, u] : Coord)) ∧
  (∀ p : Coord, Function.Injective (fderiv ℝ (ruledMap d.γ d.E) p)) ∧
  (∀ p : Coord, gaussianCurvature (inducedMetric (ruledMap d.γ d.E)) p < 0) ∧
  ∀ s : ℝ, ∃ δ > 0, ∀ v : ℝ, |v| < δ →
    let U := principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) s v
    U s = v ∧
    (∀ t ∈ Icc s (s + T), HasDerivAt U
      (-(U t / 2) * (ruledLambda d.τ t + U t * ruledD d.k d.τ t)) t) ∧
    (∀ t ∈ Icc s (s + T),
      let p : Coord := ![t, U t]
      let tangent := deriv (fun r => (![r, U r] : Coord)) t
      dotProduct tangent
        ((secondFundamental (ruledMap d.γ d.E)
          (ruledNormal (d.T t) (d.n t) (d.k t) (d.τ t) (U t)) p).mulVec tangent) = 0) ∧
    U (s + T) = v

theorem periodicRuledFrame_identity_band {T : ℝ} (d : PeriodicRuledFrame T)
    (hperiod : (∫ t in 0..T, ruledPeriodCoefficient d.k d.τ t) = 0) :
    PrincipalNormalIdentityBand d := by
  have hX : ContDiff ℝ ∞ (ruledMap d.γ d.E) :=
    (d.smooth_γ.comp (contDiff_apply ℝ ℝ 0)).add
      ((contDiff_apply ℝ ℝ 1).smul (d.smooth_E.comp (contDiff_apply ℝ ℝ 0)))
  refine ⟨hX, ?_, ?_, ?_, ?_⟩
  · intro s u
    simp only [ruledMap, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      d.period_γ s, d.period_E s]
  · intro p
    exact ruled_differential_injective (d.deriv_γ (p 0)) (d.deriv_E (p 0))
      (d.orthonormal (p 0)) (d.torsion_ne_zero (p 0))
  · intro p
    exact ruled_gaussianCurvature_neg d.deriv_γ d.deriv_E hX.contDiffOn isOpen_univ
      (fun p _ => d.orthonormal (p 0)) (fun p _ => d.torsion_ne_zero (p 0)) (mem_univ p)
  · intro s
    obtain ⟨δ, hδ, hflow⟩ := ruled_flow_over_period (s := s)
      d.smooth_k d.smooth_τ d.torsion_ne_zero d.period_k d.period_τ
    refine ⟨δ, hδ, fun v hv => ?_⟩
    obtain ⟨hinit, hderiv, hreturn⟩ := hflow v hv
    refine ⟨hinit, hderiv, ?_, ?_⟩
    · intro t ht
      have hd := hderiv t ht
      rw [(ruled_graph_hasDerivAt hd).deriv]
      apply (ruled_asymptotic_slope d.deriv_γ d.deriv_E (d.deriv_T t) (d.deriv_n t)
        (d.smooth_k.differentiable (by simp) t).hasDerivAt
        (d.smooth_τ.differentiable (by simp) t).hasDerivAt
        hX.contDiffOn isOpen_univ (mem_univ _) (d.orthonormal t) (d.torsion_ne_zero t)).mpr
      rfl
    · rw [hreturn, hperiod, mul_zero, projectiveReturn_zero]

end
end TightVer401
