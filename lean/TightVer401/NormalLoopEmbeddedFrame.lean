import TightVer401.NormalLoopEmbeddingSpeed
import TightVer401.NormalLoopEmbeddingArclength
import TightVer401.NormalLoopCriterionGeometry

namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff Manifold
set_option backward.isDefEq.respectTransparency false

theorem normalLoop_construct_embedded_balanced_frame {ζ : ℝ → Ambient} {b : ℝ → ℝ} {L η : ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (hb : ContDiff ℝ ∞ b)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1)
    (hbpos : ∀ r, 0 < b r) (hζL : Function.Periodic ζ L) (hbL : Function.Periodic b L)
    (hL : 0 < L) (hmoment : normalLoopMoment b ζ (deriv ζ) L = 0)
    (hbinj : Set.InjOn (normalLoopCurve b ζ (deriv ζ)) (Ico 0 L)) (hη : 0 < η) :
    ∃ a : ℝ → ℝ, ContDiff ℝ ∞ a ∧ Function.Periodic a L ∧ (∀ r, 0 < a r) ∧
      (∫ r in 0..L, ‖a r - b r‖) < η ∧ normalLoopMoment a ζ (deriv ζ) L = 0 ∧
      Set.InjOn (normalLoopCurve a ζ (deriv ζ)) (Ico 0 L) ∧
      ∃ e : ℝ ≃ₜ ℝ, (e : ℝ → ℝ) = rawPrimitive a ∧ ContDiff ℝ ∞ e.symm ∧
        ∃ d : PeriodicRuledFrame (rawPrimitive a L),
          d.γ = normalLoopCurve a ζ (deriv ζ) ∘ e.symm ∧
          d.T = normalLoopTangent ζ ∘ e.symm ∧ d.E = deriv ζ ∘ e.symm ∧
          d.n = ζ ∘ e.symm ∧ d.k = normalLoopPhysicalK a (normalLoopCurvature ζ) e.symm ∧
          d.τ = normalLoopPhysicalTau a e.symm ∧
          (∫ s in 0..rawPrimitive a L, ruledPeriodCoefficient d.k d.τ s) = 0 ∧
          PrincipalNormalIdentityBand d ∧
          ∃ hT : 0 < rawPrimitive a L,
            letI : Fact (0 < rawPrimitive a L) := ⟨hT⟩
            ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Ambient) ∞ d.period_γ.lift ∧
              Topology.IsEmbedding d.period_γ.lift ∧
              (∀ q, Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Ambient) d.period_γ.lift q)) := by
  obtain ⟨a, ha, haL, hapos, hsmall, hM, hB, hi, _⟩ := normalLoop_balance_embedded_speed
    hζ hb hunit hspeed hbpos hζL hbL hL hmoment hbinj hη
  obtain ⟨e, he, hesmooth, d, hγ, hT, hE, hn, hk, hτ, hperiod⟩ :=
    normalLoop_construct_periodic_ruled_frame hζ ha hunit hspeed hapos hζL haL hL hM
  have hzero : (∫ s in 0..rawPrimitive a L, ruledPeriodCoefficient d.k d.τ s) = 0 := by
    rw [hperiod, hB, mul_zero]
  have hTpos := normalLoop_arclength_period_pos ha.continuous hapos hL
  letI : Fact (0 < rawPrimitive a L) := ⟨hTpos⟩
  have hphysical : Set.InjOn d.γ (Ico 0 (rawPrimitive a L)) := by
    rw [hγ]
    exact normalLoop_arclength_reparameterized_injective ha.continuous hapos e he hi
  obtain ⟨hC, hemb⟩ := periodicCurve_lift_embedding d.smooth_γ d.period_γ hphysical
  have hderiv (s) : deriv d.γ s ≠ 0 := by
    rw [(d.deriv_γ s).deriv]
    intro hz
    have hu := (d.orthonormal s).1
    rw [hz, inner_zero_left] at hu
    norm_num at hu
  have himm := periodicCurve_lift_mfderiv_injective d.smooth_γ d.period_γ hderiv
  exact ⟨a, ha, haL, hapos, hsmall, hM, hi, e, he, hesmooth,
    d, hγ, hT, hE, hn, hk, hτ, hzero, periodicRuledFrame_identity_band d hzero,
    hTpos, hC, hemb, himm⟩

end
end TightVer401
