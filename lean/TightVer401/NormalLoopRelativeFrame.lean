import TightVer401.NormalLoopEmbeddedFrame
import TightVer401.ThinBandRuledEmbedding
import TightVer401.ThinBandRuledGauss

namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff Manifold Topology
set_option backward.isDefEq.respectTransparency false

theorem periodicPullback_representative_injective {L : ℝ} [Fact (0 < L)] {E : Type*}
    {C : AddCircle L → E} {f : ℝ → E} (hi : Function.Injective C)
    (hrep : ∀ r, C (periodProjection L r) = f r) : Set.InjOn f (Ico 0 L) := by
  intro x hx y hy he
  have hxy : C (periodProjection L x) = C (periodProjection L y) :=
    (hrep x).trans (he.trans (hrep y).symm)
  have hproj := hi hxy
  have hx' : x ∈ Ico (0 : ℝ) (0 + L) := by simpa only [zero_add] using hx
  have hy' : y ∈ Ico (0 : ℝ) (0 + L) := by simpa only [zero_add] using hy
  apply (AddCircle.coe_eq_coe_iff_of_mem_Ico hx' hy').mp
  exact hproj

theorem normalLoop_embedded_balanced_speed_band {ζ : ℝ → Ambient} {a : ℝ → ℝ} {L : ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (ha : ContDiff ℝ ∞ a)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1)
    (hapos : ∀ r, 0 < a r) (hζL : Function.Periodic ζ L) (haL : Function.Periodic a L)
    (hL : 0 < L) (hM : normalLoopMoment a ζ (deriv ζ) L = 0)
    (hB : (∫ r in 0..L, deriv (normalLoopCurvature ζ) r / Real.sqrt (a r)) = 0)
    (hi : Set.InjOn (normalLoopCurve a ζ (deriv ζ)) (Ico 0 L)) :
    ∃ e : ℝ ≃ₜ ℝ, (e : ℝ → ℝ) = rawPrimitive a ∧ ContDiff ℝ ∞ e.symm ∧
      ∃ d : PeriodicRuledFrame (rawPrimitive a L),
        d.γ = normalLoopCurve a ζ (deriv ζ) ∘ e.symm ∧
        d.T = normalLoopTangent ζ ∘ e.symm ∧ d.E = deriv ζ ∘ e.symm ∧
        d.n = ζ ∘ e.symm ∧ d.k = normalLoopPhysicalK a (normalLoopCurvature ζ) e.symm ∧
        d.τ = normalLoopPhysicalTau a e.symm ∧
        PrincipalNormalIdentityBand d ∧
        ∃ hT : 0 < rawPrimitive a L,
          letI : Fact (0 < rawPrimitive a L) := ⟨hT⟩
          Topology.IsEmbedding d.period_γ.lift ∧
          (∃ δ > 0, Topology.IsEmbedding (d.bandMap (b := δ))) ∧
          (Set.InjOn ζ (Ico 0 L) →
            ∃ δ > 0, Set.InjOn d.fullGaussMap (univ ×ˢ Icc (-δ) δ)) := by
  obtain ⟨e, he, hesmooth, d, hγ, hT, hE, hn, hk, hτ, hperiod⟩ :=
    normalLoop_construct_periodic_ruled_frame hζ ha hunit hspeed hapos hζL haL hL hM
  have hzero : (∫ s in 0..rawPrimitive a L, ruledPeriodCoefficient d.k d.τ s) = 0 := by
    rw [hperiod, hB, mul_zero]
  have hTpos := normalLoop_arclength_period_pos ha.continuous hapos hL
  letI : Fact (0 < rawPrimitive a L) := ⟨hTpos⟩
  have hphysical : Set.InjOn d.γ (Ico 0 (rawPrimitive a L)) := by
    rw [hγ]
    exact normalLoop_arclength_reparameterized_injective ha.continuous hapos e he hi
  have hiγ := periodicCurve_lift_injective d.period_γ hphysical
  obtain ⟨_, hemb⟩ := periodicCurve_lift_embedding d.smooth_γ d.period_γ hphysical
  have hband := periodicRuledFrame_exists_thin_band_embedding d hiγ
  refine ⟨e, he, hesmooth, d, hγ, hT, hE, hn, hk, hτ,
    periodicRuledFrame_identity_band d hzero, hTpos, hemb, hband, ?_⟩
  intro hζinj
  have hnrep : Set.InjOn d.n (Ico 0 (rawPrimitive a L)) := by
    rw [hn]
    exact normalLoop_arclength_reparameterized_injective ha.continuous hapos e he hζinj
  exact periodicRuledFrame_exists_thin_Gauss_injective d
    (periodicCurve_lift_injective d.period_n hnrep)

end
end TightVer401
