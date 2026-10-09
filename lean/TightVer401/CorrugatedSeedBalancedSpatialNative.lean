import TightVer401.CorrugatedSeedBalancedSpatial
import TightVer401.NormalLoopEmbeddingPeriod

namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff Manifold Topology

theorem corrugatedSeedBalancedSpatial_periodic {N ell L : ℝ} {ψ a : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (ha : Continuous a) (haL : Function.Periodic a L)
    (hPL : Function.Periodic (normalLoopTangent (corrugatedSeedSphere N ∘ ψ)) L)
    (hclose : (∫ r in 0..L, a r • normalLoopTangent (corrugatedSeedSphere N ∘ ψ) r) = 0) :
    Function.Periodic (corrugatedSeedBalancedSpatial N ψ ell a) L := by
  have hp := speedCurve_periodic ha
    (normalLoop_actual_smooth ((corrugatedSeedSphere_contDiff N).comp hψ)).1.continuous haL hPL hclose
  intro r
  unfold corrugatedSeedBalancedSpatial
  rw [hp r]

theorem corrugatedSeedBalancedSpatial_native_embedding {N ell L : ℝ} [Fact (0 < L)]
    (hN : 1 < N) {ψ a : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hi : ∀ r, HasDerivAt ψ (corrugatedSeedSphericalSpeed N (ψ r))⁻¹ r)
    (ha : ContDiff ℝ ∞ a) (hapos : ∀ r, 0 < a r) (haL : Function.Periodic a L)
    (hPL : Function.Periodic (normalLoopTangent (corrugatedSeedSphere N ∘ ψ)) L)
    (hclose : (∫ r in 0..L, a r • normalLoopTangent (corrugatedSeedSphere N ∘ ψ) r) = 0)
    (hhinj : InjOn (covariantSpeedCurve ell (corrugatedSeedRotation N) a
      (corrugatedSeedFrameHorizontal N ψ)) (Ico 0 L)) :
    ∃ C : AddCircle L → Ambient, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Ambient) ∞ C ∧
      Topology.IsEmbedding C ∧
      (∀ q, Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Ambient) C q)) ∧
      (∀ r, C (periodProjection L r) = corrugatedSeedBalancedSpatial N ψ ell a r) := by
  have hp := corrugatedSeedBalancedSpatial_periodic (ell := ell) hψ ha.continuous haL hPL hclose
  have hs := corrugatedSeedBalancedSpatial_contDiff N ell hψ ha
  have hj := corrugatedSeedBalancedSpatial_injOn hψ ha.continuous hhinj
  obtain ⟨hC, hemb⟩ := periodicCurve_lift_embedding hs hp hj
  have hderiv (r : ℝ) : deriv (corrugatedSeedBalancedSpatial N ψ ell a) r ≠ 0 := by
    rw [(corrugatedSeedBalancedSpatial_hasDerivAt N ell hψ ha.continuous r).deriv]
    apply smul_ne_zero (hapos r).ne'
    intro hz
    exact corrugatedSeedFrameHorizontal_ne_zero hN hψ hi r (by
      unfold corrugatedSeedFrameHorizontal
      rw [hz]
      exact (corrugatedAmbientHorizontalCLM_apply 0).symm.trans (map_zero _))
  exact ⟨hp.lift, hC, hemb, periodicCurve_lift_mfderiv_injective hs hp hderiv, hp.lift_coe⟩

end
end TightVer401
