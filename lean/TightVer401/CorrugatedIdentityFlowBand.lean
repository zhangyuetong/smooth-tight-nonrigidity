import TightVer401.CorrugatedIdentityBand
import TightVer401.IdentityBandSaturatedAnnulus

namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff Manifold Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
local instance corrugatedIdentityFlowBandSphereDimension : Fact (Module.finrank ℝ Ambient = 2 + 1) :=
  ⟨by simp [Ambient]⟩

/-- A smooth immersed embedded annulus, whose constant-initial-value circles
are complete closed actual asymptotic leaves inside the selected band. -/
def SaturatedIdentitySubband {T : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T) (w : ℝ) : Prop :=
  ∃ hbalance : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0,
    ∃ δ > 0, δ < w ∧
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Ambient) ∞
        (identityFlowSurface (δ := δ) d hbalance 0) ∧
      (∀ p : AddCircle T × Ioo (0 : ℝ) δ,
        Function.Injective (bandDifferential (identityFlowSurface (δ := δ) d hbalance 0) p)) ∧
      Topology.IsEmbedding (identityFlowSurface (δ := δ) d hbalance 0) ∧
      ∀ v : Ioo (0 : ℝ) δ,
        let U := principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 v
        U 0 = v ∧ Function.Periodic U T ∧ ContDiff ℝ ∞ U ∧
        (∀ t : ℝ, U t ∈ Ioo 0 w) ∧
        (∀ t : ℝ, HasDerivAt U
          (-(U t / 2) * (ruledLambda d.τ t + U t * ruledD d.k d.τ t)) t) ∧
        (∀ t : ℝ,
          let p : Coord := ![t, U t]
          let tangent := deriv (fun r => (![r, U r] : Coord)) t
          dotProduct tangent
            ((secondFundamental (ruledMap d.γ d.E)
              (ruledNormal (d.T t) (d.n t) (d.k t) (d.τ t) (U t)) p).mulVec tangent) = 0)

theorem periodicRuledFrame_saturatedIdentitySubband {T w : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T) (hidentity : PrincipalNormalIdentityBand d)
    (hw : 0 < w) (hband : Topology.IsEmbedding (d.bandMap (b := w))) :
    SaturatedIdentitySubband d w := by
  refine ⟨periodicRuledFrame_identity_band_period_zero d hidentity, ?_⟩
  obtain ⟨δ, hδ, hδw, hsmooth, hemb, himm, hleaves⟩ :=
    periodicRuledFrame_exists_embedded_flow_annulus d hidentity 0 hw hband
  exact ⟨δ, hδ, hδw, hsmooth, himm, hemb, hleaves⟩

/-- The exact seed constructs its embedded identity band and a native protected
annulus of complete closed asymptotic leaves in that same band.
The bending in CompleteIdentityBand is supported in the original band;
this statement does not place its support inside this particular subannulus. -/
theorem corrugatedSeed_exists_protected_identity_holonomy_band {N : ℕ} (hN : 10000 ≤ N)
    {η : ℝ} (hη : 0 < η) :
    let ell := corrugatedSeedArcCell (N : ℝ)
    let L := (N : ℝ) * ell
    ∃ e : ℝ ≃ₜ ℝ, (e : ℝ → ℝ) = corrugatedSeedArcMap (N : ℝ) ∧
      ContDiff ℝ ∞ e.symm ∧
      ∃ a : ℝ → ℝ, ContDiff ℝ ∞ a ∧ Function.Periodic a ell ∧ (∀ r, 0 < a r) ∧
        (∫ r in 0..ell, ‖a r - corrugatedSeedInitialSpeed (N : ℝ) e.symm r‖) < η ∧
        (∫ r in 0..L, a r • normalLoopTangent (corrugatedSeedSphere (N : ℝ) ∘ e.symm) r) = 0 ∧
        (∫ r in 0..L, deriv (normalLoopCurvature (corrugatedSeedSphere (N : ℝ) ∘ e.symm)) r /
          Real.sqrt (a r)) = 0 ∧
        ComplexVisiblePair (1 / 4) (corrugatedSeedBeta (N : ℝ) ∘ e.symm)
          (corrugatedSeedBalancedPartner (N : ℝ) e.symm ell a) ∧
        ComplexVisiblePair (4 / 5)
          (corrugatedReverseReflect (corrugatedSeedBalancedPartner (N : ℝ) e.symm ell a))
          (corrugatedReverseReflect (corrugatedSeedBeta (N : ℝ) ∘ e.symm)) ∧
        ∃ S : ℝ ≃ₜ ℝ, (S : ℝ → ℝ) = rawPrimitive a ∧ ContDiff ℝ ∞ S.symm ∧
          ∃ d : PeriodicRuledFrame (rawPrimitive a L),
            d.γ = corrugatedSeedBalancedSpatial (N : ℝ) e.symm ell a ∘ S.symm ∧
            d.T = normalLoopTangent (corrugatedSeedSphere (N : ℝ) ∘ e.symm) ∘ S.symm ∧
            d.E = deriv (corrugatedSeedSphere (N : ℝ) ∘ e.symm) ∘ S.symm ∧
            d.n = (corrugatedSeedSphere (N : ℝ) ∘ e.symm) ∘ S.symm ∧
            d.k = normalLoopPhysicalK a
              (normalLoopCurvature (corrugatedSeedSphere (N : ℝ) ∘ e.symm)) S.symm ∧
            d.τ = normalLoopPhysicalTau a S.symm ∧ PrincipalNormalIdentityBand d ∧
            ∃ hT : 0 < rawPrimitive a L,
              letI : Fact (0 < rawPrimitive a L) := ⟨hT⟩
              ∃ w > 0,
                ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Ambient) ∞ (d.bandMap (b := w)) ∧
                (∀ p : AddCircle (rawPrimitive a L) × Ioo (0 : ℝ) w,
                  Function.Injective (bandDifferential (d.bandMap (b := w)) p)) ∧
                Topology.IsEmbedding (d.bandMap (b := w)) ∧
                Topology.IsEmbedding (corrugatedAmbientHorizontalCLM ∘ d.bandMap (b := w)) ∧
                ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℂ) ∞
                  (corrugatedAmbientHorizontalCLM ∘ d.bandMap (b := w)) ∧
                (∀ p : AddCircle (rawPrimitive a L) × Ioo (0 : ℝ) w,
                  Function.Injective (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℂ)
                    (corrugatedAmbientHorizontalCLM ∘ d.bandMap (b := w)) p)) ∧
                Function.Injective (fun p : AddCircle (rawPrimitive a L) × Ioo (0 : ℝ) w =>
                  d.fullGaussMap (p.1, (p.2 : ℝ))) ∧
                (∀ p : AddCircle (rawPrimitive a L) × Ioo (0 : ℝ) w,
                  0 < d.fullGaussMap (p.1, (p.2 : ℝ)) 2) ∧
                ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓡 2) ∞ (d.bandSphereGauss (b := w)) ∧
                Function.Injective (d.bandSphereGauss (b := w)) ∧
                (∀ p : AddCircle (rawPrimitive a L) × Ioo (0 : ℝ) w,
                  Function.Injective (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓡 2)
                    (d.bandSphereGauss (b := w)) p)) ∧
                (∀ p : AddCircle (rawPrimitive a L) × Ioo (0 : ℝ) w, ∀ v : ℝ × ℝ,
                  inner ℝ (bandDifferential (d.bandMap (b := w)) p v) (d.bandGaussMap p) = 0) ∧
                IdentityReturnInsideBand d w ∧ CompleteIdentityBand d w ∧ SaturatedIdentitySubband d w := by
  dsimp only
  obtain ⟨e, he, hψ, a, ha, haT, hapos, hsmall, hMfull, hBfull, hout, href,
    S, hS, hSsmooth, d, hγ, hT, hE, hn, hk, hτ, hidentity, hTpos, w, hw,
    hsmooth, himm, hemb, hproj, hprojs, hproji, hgauss, hnorth, hGs, hGinj, hGdiff,
    horth, hreturn, hcomplete⟩ := corrugatedSeed_exists_identity_holonomy_band hN hη
  letI : Fact (0 < rawPrimitive a ((N : ℝ) * corrugatedSeedArcCell (N : ℝ))) := ⟨hTpos⟩
  exact ⟨e, he, hψ, a, ha, haT, hapos, hsmall, hMfull, hBfull, hout, href,
    S, hS, hSsmooth, d, hγ, hT, hE, hn, hk, hτ, hidentity, hTpos, w, hw,
    hsmooth, himm, hemb, hproj, hprojs, hproji, hgauss, hnorth, hGs, hGinj, hGdiff,
    horth, hreturn, hcomplete, periodicRuledFrame_saturatedIdentitySubband d hidentity hw hemb⟩

end
end TightVer401
