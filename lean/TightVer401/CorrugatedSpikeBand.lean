import TightVer401.CorrugatedSpike
import TightVer401.NormalLoopProjectedBand
import TightVer401.ThinBandRuledNorth

namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff Manifold Topology
set_option backward.isDefEq.respectTransparency false

/-- The very same balanced seed speed supplies the actual arclength frame and
identity-return negative-curvature band, with actual thin projection and
Gauss injectivity. This accepts ordinary speed equations, rather than a band. -/
theorem corrugatedSeed_balanced_speed_band {N : ℕ} (hN : 10000 ≤ N)
    (e : ℝ ≃ₜ ℝ) (he : (e : ℝ → ℝ) = corrugatedSeedArcMap (N : ℝ))
    (hψ : ContDiff ℝ ∞ e.symm)
    (hi : ∀ r, HasDerivAt e.symm (corrugatedSeedSphericalSpeed (N : ℝ) (e.symm r))⁻¹ r)
    {a : ℝ → ℝ} (ha : ContDiff ℝ ∞ a)
    (haT : Function.Periodic a (corrugatedSeedArcCell (N : ℝ))) (hapos : ∀ r, 0 < a r)
    (hclose : (∫ r in 0..((N : ℝ) * corrugatedSeedArcCell (N : ℝ)),
      a r • normalLoopTangent (corrugatedSeedSphere (N : ℝ) ∘ e.symm) r) = 0)
    (hbalance : (∫ r in 0..((N : ℝ) * corrugatedSeedArcCell (N : ℝ)),
      deriv (normalLoopCurvature (corrugatedSeedSphere (N : ℝ) ∘ e.symm)) r / Real.sqrt (a r)) = 0)
    (hhinj : Set.InjOn (covariantSpeedCurve (corrugatedSeedArcCell (N : ℝ))
      (corrugatedSeedRotation (N : ℝ)) a (corrugatedSeedFrameHorizontal (N : ℝ) e.symm))
      (Ico 0 ((N : ℝ) * corrugatedSeedArcCell (N : ℝ)))) :
    let L := (N : ℝ) * corrugatedSeedArcCell (N : ℝ)
    let ζ := corrugatedSeedSphere (N : ℝ) ∘ e.symm
    ∃ S : ℝ ≃ₜ ℝ, (S : ℝ → ℝ) = rawPrimitive a ∧ ContDiff ℝ ∞ S.symm ∧
      ∃ d : PeriodicRuledFrame (rawPrimitive a L),
        d.γ = normalLoopCurve a ζ (deriv ζ) ∘ S.symm ∧
        d.T = normalLoopTangent ζ ∘ S.symm ∧ d.E = deriv ζ ∘ S.symm ∧
        d.n = ζ ∘ S.symm ∧ d.k = normalLoopPhysicalK a (normalLoopCurvature ζ) S.symm ∧
        d.τ = normalLoopPhysicalTau a S.symm ∧ PrincipalNormalIdentityBand d ∧
        ∃ hT : 0 < rawPrimitive a L,
          letI : Fact (0 < rawPrimitive a L) := ⟨hT⟩
          (∃ δ > 0, Topology.IsEmbedding (d.bandMap (b := δ)) ∧
            Topology.IsEmbedding (corrugatedAmbientHorizontalCLM ∘ d.bandMap (b := δ)) ∧
            Function.Injective (fun p : AddCircle (rawPrimitive a L) × Ioo (0 : ℝ) δ =>
              d.fullGaussMap (p.1, (p.2 : ℝ)))) ∧
          (∃ δ > 0, ∀ p ∈ (univ ×ˢ Icc (-δ) δ : Set (AddCircle (rawPrimitive a L) × ℝ)),
            0 < d.fullGaussMap p 2) := by
  dsimp only
  let ζ := corrugatedSeedSphere (N : ℝ) ∘ e.symm
  let P := normalLoopTangent ζ
  let Ph := corrugatedSeedFrameHorizontal (N : ℝ) e.symm
  let L := (N : ℝ) * corrugatedSeedArcCell (N : ℝ)
  have hnormal := corrugatedSeed_spike_normal (by omega : 2 ≤ N) e he hψ hi
  have hP := (normalLoop_actual_smooth hnormal.2.1).1
  have hPhEq : corrugatedAmbientHorizontalCLM ∘ P = Ph := by
    funext r
    exact corrugatedAmbientHorizontalCLM_apply (P r)
  have hip : Set.InjOn (speedCurve a Ph) (Ico 0 L) :=
    (covariantSpeedCurve_injOn_iff (T := corrugatedSeedArcCell (N : ℝ))
      (ξ := corrugatedSeedRotation (N : ℝ)) (Ico 0 L)).mp hhinj
  have hcurve : corrugatedAmbientHorizontalCLM ∘ normalLoopCurve a ζ (deriv ζ) = speedCurve a Ph := by
    funext r
    change corrugatedAmbientHorizontalCLM (speedCurve a P r) = speedCurve a Ph r
    rw [← hPhEq]
    exact (speedCurve_linear_projection corrugatedAmbientHorizontalCLM ha.continuous hP.continuous r).symm
  have hiπ : Set.InjOn (corrugatedAmbientHorizontalCLM ∘ normalLoopCurve a ζ (deriv ζ)) (Ico 0 L) := by
    rw [hcurve]
    exact hip
  obtain ⟨S, hS, hsmooth, d, hγ, hT, hE, hn, hk, hτ, hidentity, hTpos, hwidth⟩ :=
    normalLoop_northern_embedded_balanced_band hnormal.2.1 ha hnormal.2.2.2.2.1
      hnormal.2.2.2.2.2.1 hapos hnormal.2.2.1 (haT.nat_mul N) hnormal.1
      hclose hbalance hnormal.2.2.2.1 hnormal.2.2.2.2.2.2 hiπ
  letI : Fact (0 < rawPrimitive a L) := ⟨hTpos⟩
  have hnorthd : ∀ r, 0 < d.n r 2 := by
    intro r
    rw [hn]
    exact hnormal.2.2.2.2.2.2 (S.symm r)
  exact ⟨S, hS, hsmooth, d, hγ, hT, hE, hn, hk, hτ, hidentity, hTpos,
    hwidth, periodicRuledFrame_exists_northern_strip d hnorthd⟩

end
end TightVer401
