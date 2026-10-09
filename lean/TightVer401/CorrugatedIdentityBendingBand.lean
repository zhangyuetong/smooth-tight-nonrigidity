import TightVer401.CorrugatedIdentityFlowBand
import TightVer401.IdentityBandProtectedBending
import TightVer401.IdentityBandBendingPullback
import TightVer401.BandBendingBranches

namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff Manifold Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
local instance corrugatedIdentityBendingBandSphereDimension : Fact (Module.finrank ℝ Ambient = 2 + 1) :=
  ⟨by simp [Ambient]⟩

/-- The same actual flow annulus contains the full support of a genuine
nonzero compact bending. Its pullback is a nonzero compact bending on the
annulus and gives exact common metrics for opposite perturbations. -/
def ProtectedIdentityBendingSubband {T : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T) (w : ℝ) : Prop :=
  ∃ hbalance : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0,
    ∃ δ > 0, δ < w ∧
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Ambient) ∞
        (identityFlowSurface (δ := δ) d hbalance 0) ∧
      (∀ p : AddCircle T × Ioo (0 : ℝ) δ,
        Function.Injective (bandDifferential (identityFlowSurface (δ := δ) d hbalance 0) p)) ∧
      Topology.IsEmbedding (identityFlowSurface (δ := δ) d hbalance 0) ∧
      ∃ hinside : ∀ v ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
        principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 v t ∈ Ioo 0 w,
      ∃ Y : AddCircle T × Ioo (0 : ℝ) w → Ambient,
        IsBandBending (d.bandMap (b := w)) Y ∧ HasCompactSupport Y ∧
        (∃ p, Y p ≠ 0) ∧
        (fun p : AddCircle T × Ioo (0 : ℝ) w => (p.1, (p.2 : ℝ))) '' tsupport Y ⊆
          range (identityFlowCoordinates (δ := δ) d hbalance 0) ∧
        d.bandMap '' tsupport Y ⊆ range (identityFlowSurface (δ := δ) d hbalance 0) ∧
        (let Yflow := Y ∘ identityFlowBandInclusion d hbalance 0 hinside
         IsBandBending (identityFlowSurface (δ := δ) d hbalance 0) Yflow ∧
         HasCompactSupport Yflow ∧ (∃ p, Yflow p ≠ 0) ∧
         ∀ ε : ℝ, bandInducedForm (identityFlowSurface (δ := δ) d hbalance 0 + ε • Yflow) =
           bandInducedForm (identityFlowSurface (δ := δ) d hbalance 0 - ε • Yflow) ∧
           ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Ambient) ∞
             (identityFlowSurface (δ := δ) d hbalance 0 + ε • Yflow) ∧
           ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Ambient) ∞
             (identityFlowSurface (δ := δ) d hbalance 0 - ε • Yflow) ∧
           (∀ p : AddCircle T × Ioo (0 : ℝ) δ,
             Function.Injective (bandDifferential (identityFlowSurface (δ := δ) d hbalance 0 + ε • Yflow) p) ∧
             Function.Injective (bandDifferential (identityFlowSurface (δ := δ) d hbalance 0 - ε • Yflow) p)) ∧
           (ε ≠ 0 → identityFlowSurface (δ := δ) d hbalance 0 + ε • Yflow ≠
             identityFlowSurface (δ := δ) d hbalance 0 - ε • Yflow)) ∧
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

theorem periodicRuledFrame_protectedIdentityBendingSubband {T w : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T) (hidentity : PrincipalNormalIdentityBand d)
    (hw : 0 < w) (hband : Topology.IsEmbedding (d.bandMap (b := w))) :
    ProtectedIdentityBendingSubband d w := by
  let hbalance := periodicRuledFrame_identity_band_period_zero d hidentity
  obtain ⟨δ, hδ, hδw, hsmooth, hemb, himm, hleaves⟩ :=
    periodicRuledFrame_exists_embedded_flow_annulus d hidentity 0 hw hband
  have hinside : ∀ v ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 v t ∈ Ioo 0 w := by
    intro v hv
    exact (hleaves ⟨v, hv⟩).2.2.2.1
  have hden : ∀ v ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      1 + ruledRho d.τ 0 * v * (ruledOmega d.k d.τ t - ruledOmega d.k d.τ 0) ≠ 0 := by
    intro v hv t hz
    have hp := (hinside v hv t).1
    simp [principalTrajectory, hz] at hp
  obtain ⟨Y, hY, hcompact, hnonzero, hsupport, hsurfaceSupport⟩ :=
    periodicRuledFrame_exists_protected_bending d hidentity 0 hw hδ
  obtain ⟨hYflow, hYflowcompact, hYflownonzero⟩ :=
    identityFlowSurface_compact_nonzero_bending d hbalance 0 hden hinside
      hY hcompact hnonzero hsupport
  refine ⟨hbalance, δ, hδ, hδw, hsmooth, himm, hemb, hinside, Y,
    hY, hcompact, hnonzero, hsupport, hsurfaceSupport,
    ⟨hYflow, hYflowcompact, hYflownonzero, ?_⟩, hleaves⟩
  intro ε
  obtain ⟨hplus, hminus⟩ := bandBending_branches_contMDiff hsmooth hYflow ε
  exact ⟨bandBending_opposite_branches_metric hsmooth hYflow ε, hplus, hminus,
    fun p => bandBending_opposite_branches_immersion hsmooth hYflow ε p (himm p),
    fun hε => bandBending_opposite_branches_ne hε hYflownonzero⟩

/-- The exact corrected seed constructs the identity band, its protected closed-leaf
annulus, and genuine localized bending with the precise protected support. -/
theorem corrugatedSeed_exists_protected_identity_band_bending {N : ℕ} (hN : 10000 ≤ N)
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
                IdentityReturnInsideBand d w ∧ CompleteIdentityBand d w ∧ SaturatedIdentitySubband d w ∧ ProtectedIdentityBendingSubband d w := by
  dsimp only
  obtain ⟨e, he, hψ, a, ha, haT, hapos, hsmall, hMfull, hBfull, hout, href,
    S, hS, hSsmooth, d, hγ, hT, hE, hn, hk, hτ, hidentity, hTpos, w, hw,
    hsmooth, himm, hemb, hproj, hprojs, hproji, hgauss, hnorth, hGs, hGinj, hGdiff,
    horth, hreturn, hcomplete, hsaturated⟩ :=
      corrugatedSeed_exists_protected_identity_holonomy_band hN hη
  letI : Fact (0 < rawPrimitive a ((N : ℝ) * corrugatedSeedArcCell (N : ℝ))) := ⟨hTpos⟩
  exact ⟨e, he, hψ, a, ha, haT, hapos, hsmall, hMfull, hBfull, hout, href,
    S, hS, hSsmooth, d, hγ, hT, hE, hn, hk, hτ, hidentity, hTpos, w, hw,
    hsmooth, himm, hemb, hproj, hprojs, hproji, hgauss, hnorth, hGs, hGinj, hGdiff,
    horth, hreturn, hcomplete, hsaturated,
    periodicRuledFrame_protectedIdentityBendingSubband d hidentity hw hemb⟩

end
end TightVer401
