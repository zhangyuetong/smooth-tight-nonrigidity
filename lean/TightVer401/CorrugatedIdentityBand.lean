import TightVer401.CorrugatedSpikeActualBand
import TightVer401.NormalLoopCriterionBandFlow
import TightVer401.IdentityBandGlobalFlow
import TightVer401.IdentityBandPeriodKernel
import TightVer401.PeriodicRuledNativeGauss
import TightVer401.PeriodicRuledNativeProjection

/-! The actual seed constructs one balanced embedded band with identity holonomy.
All existence inputs are the seed index and the requested L1 tolerance.
The same corrected speed and translated spatial primitive are retained. -/
namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff Manifold Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
local instance corrugatedIdentityBandSphereDimension : Fact (Module.finrank ℝ Ambient = 2 + 1) :=
  ⟨by simp [Ambient]⟩

/-- The actual return is the identity and its trajectories remain in the selected band. -/
def IdentityReturnInsideBand {T : ℝ} (d : PeriodicRuledFrame T) (w : ℝ) : Prop :=
  ∀ s : ℝ, ∃ δ > 0, δ < w ∧ ∀ v : ℝ, 0 < v → v < δ →
    let U := principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) s v
    U s = v ∧ (∀ t ∈ Icc s (s + T), U t ∈ Ioo 0 w) ∧ U (s + T) = v

theorem periodicRuledFrame_identityReturnInsideBand {T : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T) (hidentity : PrincipalNormalIdentityBand d)
    {w : ℝ} (hw : 0 < w) : IdentityReturnInsideBand d w := by
  intro s
  obtain ⟨δ, hδ, hδw, hf⟩ := periodicRuledFrame_identity_flow_inside_band d hidentity s w hw
  refine ⟨δ, hδ, hδw, fun v hv hvδ => ?_⟩
  obtain ⟨hinit, hinside, _hode, _hasym, hreturn⟩ := hf v hv hvδ
  exact ⟨hinit, hinside, hreturn⟩

/-- Complete closed asymptotic leaves and a genuine nonzero localized bending,
all on the same actual geometric band and for the same actual frame. -/
def CompleteIdentityBand {T : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T) (w : ℝ) : Prop :=
  (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0 ∧
  (∀ s : ℝ, ∃ δ > 0, δ < w ∧ ∀ v : ℝ, 0 < v → v < δ →
    let U := principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) s v
    U s = v ∧ Function.Periodic U T ∧ ContDiff ℝ ∞ U ∧
    (∀ t : ℝ, U t ∈ Ioo 0 w) ∧
    (∀ t : ℝ, HasDerivAt U
      (-(U t / 2) * (ruledLambda d.τ t + U t * ruledD d.k d.τ t)) t) ∧
    (∀ t : ℝ,
      let p : Coord := ![t, U t]
      let tangent := deriv (fun r => (![r, U r] : Coord)) t
      dotProduct tangent
        ((secondFundamental (ruledMap d.γ d.E)
          (ruledNormal (d.T t) (d.n t) (d.k t) (d.τ t) (U t)) p).mulVec tangent) = 0)) ∧
  (∃ Y : AddCircle T × Ioo (0 : ℝ) w → Ambient,
    IsBandBending (d.bandMap (b := w)) Y ∧ HasCompactSupport Y ∧ ∃ p, Y p ≠ 0)

theorem periodicRuledFrame_completeIdentityBand {T : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T) (hidentity : PrincipalNormalIdentityBand d)
    {w : ℝ} (hw : 0 < w) : CompleteIdentityBand d w := by
  have hperiod := periodicRuledFrame_identity_band_period_zero d hidentity
  exact ⟨hperiod, fun s => periodicRuledFrame_closed_asymptotic_leaves d hperiod s w hw,
    periodicRuledFrame_identity_band_localized_bending d hidentity hw⟩

/-- Construct the balanced speed, both arclength maps and the embedded
identity-holonomy band from the exact corrugated seed. -/
theorem corrugatedSeed_exists_identity_holonomy_band {N : ℕ} (hN : 10000 ≤ N)
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
                IdentityReturnInsideBand d w ∧ CompleteIdentityBand d w := by
  dsimp only
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNlarge : (10000 : ℝ) ≤ N := by exact_mod_cast hN
  let ell := corrugatedSeedArcCell (N : ℝ)
  let L := (N : ℝ) * ell
  letI : Fact (0 < ell) := ⟨corrugatedSeedArcCell_pos hNr⟩
  obtain ⟨e, he, hψ, hi, _hc⟩ := corrugatedSeed_exists_cell_arclength hNr
  obtain ⟨a, ha, haT, hapos, hsmall, _hMcell, hMfull, _hBcell, hBfull,
    _hiRaw, hiCov, hvis, _hsupport⟩ :=
    corrugatedSeed_spike_speed hN e he hψ hi hη (show 0 < (1 : ℝ) by norm_num)
  have hout := corrugatedSeedBalancedPartner_outer_visible hψ ha hapos hvis
  have href := corrugatedSeedBalancedPartner_reflected_visible (ell := ell) hNlarge hψ hi ha hapos
  obtain ⟨S, hS, hSsmooth, d, hγ, hT, hE, hn, hk, hτ, hidentity, hTpos,
    w, hw, hemb, hproj, hgauss, hnorth⟩ :=
    corrugatedSeed_balanced_actual_band hN e he hψ hi ha haT hapos hMfull hBfull hiCov
  letI : Fact (0 < rawPrimitive a L) := ⟨hTpos⟩
  have hprojection := periodicRuledFrame_northern_band_projection_regular d hnorth
  exact ⟨e, he, hψ, a, ha, haT, hapos, hsmall, hMfull, hBfull, hout, href,
    S, hS, hSsmooth, d, hγ, hT, hE, hn, hk, hτ, hidentity, hTpos, w, hw,
    d.bandMap_contMDiff, (fun p => periodicRuledFrame_bandMap_immersion d p),
    hemb, hproj, hprojection.1, hprojection.2, hgauss, hnorth, periodicRuledFrame_bandSphereGauss_contMDiff d,
    periodicRuledFrame_bandSphereGauss_injective_of_actual d hgauss,
    (fun p => periodicRuledFrame_bandSphereGauss_differential_injective d p),
    periodicRuledFrame_bandGaussMap_orthogonal d,
    periodicRuledFrame_identityReturnInsideBand d hidentity hw,
    periodicRuledFrame_completeIdentityBand d hidentity hw⟩

end
end TightVer401
