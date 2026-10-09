import TightVer401.IdentityBandPlanarSupportBand

/-! Construction of the actual planar support annulus for the particular
corrected identity band, starting only from the retained seed parameters. -/
open scoped Manifold
namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- The same corrected speed/frame and protected native identity band admit
one actual Cartesian support potential, with source and gradient diffeomorphisms
onto their actual open annuli and the precise retained bending support image. -/
theorem identityBand_exists_planar_support_annulus {N : ℕ} (hN : 10000 ≤ N)
    {η : ℝ} (hη : 0 < η) :
    let ell := corrugatedSeedArcCell (N : ℝ)
    let L := (N : ℝ) * ell
    ∃ e : ℝ ≃ₜ ℝ, (e : ℝ → ℝ) = corrugatedSeedArcMap (N : ℝ) ∧
      ContDiff ℝ ∞ e.symm ∧
      ∃ a : ℝ → ℝ, ContDiff ℝ ∞ a ∧ Function.Periodic a ell ∧ (∀ r, 0 < a r) ∧
        (∫ r in 0..ell, ‖a r - corrugatedSeedInitialSpeed (N : ℝ) e.symm r‖) < η ∧
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
              ∃ w > 0, Topology.IsEmbedding (d.bandMap (b := w)) ∧
                ProtectedIdentityBendingSubband d w ∧ IdentityBandPlanarSupportAnnulus d w := by
  dsimp only
  obtain ⟨e, he, hψ, a, ha, haT, hapos, hsmall, _hMfull, _hBfull, _hout, _href,
    S, hS, hSsmooth, d, hγ, hT, hE, hn, hk, hτ, hidentity, hTpos, w, hw,
    _hsmooth, _himm, hemb, hproj, hprojs, hproji, _hgauss, hnorth, _hGs, hGinj, _hGdiff,
    _horth, _hreturn, _hcomplete, _hsaturated, hprotected⟩ :=
      corrugatedSeed_exists_protected_identity_band_bending hN hη
  letI : Fact (0 < rawPrimitive a ((N : ℝ) * corrugatedSeedArcCell (N : ℝ))) := ⟨hTpos⟩
  exact ⟨e, he, hψ, a, ha, haT, hapos, hsmall, S, hS, hSsmooth,
    d, hγ, hT, hE, hn, hk, hτ, hidentity, hTpos, w, hw, hemb, hprotected,
    identityBandPlanarSupport_actual_band d hw hGinj hnorth hproj hprojs hproji hprotected⟩

end
end TightVer401