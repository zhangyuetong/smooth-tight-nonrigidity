import TightVer401.CorrugatedSpikeActualBand
import TightVer401.NormalLoopEmbeddingArclength
import TightVer401.NormalLoopEmbeddingPeriod

/-! Same corrected seed, arclength frame, and central geometric injectivity.
The correction is chosen once with its actual horizontal injectivity retained.
This precedes any final collar width or protected bending selection. -/
namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff Manifold Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- Construct the corrected frame together with the central hypotheses for a
two-sided thin collar. The same actual speed supplies closure, holonomy balance,
visibility and both central circle injections. No collar, potential, inverse or
protected bending field is assumed or chosen here. -/
theorem identityBandCentralSupport_seed_geometry {N : ℕ} (hN : 10000 ≤ N)
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
        Set.InjOn (covariantSpeedCurve ell (corrugatedSeedRotation (N : ℝ)) a
          (corrugatedSeedFrameHorizontal (N : ℝ) e.symm)) (Ico 0 L) ∧
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
              Function.Injective d.period_n.lift ∧ (∀ s, 0 < d.n s 2) ∧
              Function.Injective (corrugatedAmbientHorizontalCLM ∘ d.period_γ.lift) ∧
              ∃ oldw > 0, Topology.IsEmbedding (d.bandMap (b := oldw)) ∧
                Topology.IsEmbedding (corrugatedAmbientHorizontalCLM ∘ d.bandMap (b := oldw)) := by
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
  have hnormal := corrugatedSeed_spike_normal (by omega : 2 ≤ N) e he hψ hi
  obtain ⟨S, hS, hSsmooth, d, hγ, hT, hE, hn, hk, hτ, hidentity, hTpos,
    oldw, holdw, hemb, hproj, _hgauss, _hnorth⟩ :=
      corrugatedSeed_balanced_actual_band hN e he hψ hi ha haT hapos hMfull hBfull hiCov
  letI : Fact (0 < rawPrimitive a L) := ⟨hTpos⟩
  have hin : Set.InjOn d.n (Ico 0 (rawPrimitive a L)) := by
    rw [hn]
    exact normalLoop_arclength_reparameterized_injective ha.continuous hapos S hS
      hnormal.2.2.2.1
  have hnorthd : ∀ s, 0 < d.n s 2 := by
    intro s
    rw [hn]
    exact hnormal.2.2.2.2.2.2 (S.symm s)
  have hiπ : Set.InjOn
      (corrugatedAmbientHorizontalCLM ∘ corrugatedSeedBalancedSpatial (N : ℝ) e.symm ell a)
      (Ico 0 L) := by
    intro s hs t ht hst
    apply hiCov hs ht
    simpa only [Function.comp_apply, corrugatedAmbientHorizontalCLM_apply,
      corrugatedSeedBalancedSpatial_horizontal (N : ℝ) ell hψ ha.continuous] using hst
  have hip : Set.InjOn (corrugatedAmbientHorizontalCLM ∘ d.γ)
      (Ico 0 (rawPrimitive a L)) := by
    rw [hγ]
    exact normalLoop_arclength_reparameterized_injective ha.continuous hapos S hS hiπ
  have hp : Function.Periodic (corrugatedAmbientHorizontalCLM ∘ d.γ) (rawPrimitive a L) := by
    intro s
    change corrugatedAmbientHorizontalCLM (d.γ (s + rawPrimitive a L)) =
      corrugatedAmbientHorizontalCLM (d.γ s)
    rw [d.period_γ s]
  have hlift : hp.lift = corrugatedAmbientHorizontalCLM ∘ d.period_γ.lift := by
    funext q
    obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective q
    simp only [Function.comp_apply, Function.Periodic.lift_coe]
  have hipnative : Function.Injective (corrugatedAmbientHorizontalCLM ∘ d.period_γ.lift) := by
    rw [← hlift]
    exact periodicCurve_lift_injective hp hip
  exact ⟨e, he, hψ, a, ha, haT, hapos, hsmall, hMfull, hBfull, hout, href, hiCov,
    S, hS, hSsmooth, d, hγ, hT, hE, hn, hk, hτ, hidentity, hTpos,
    periodicCurve_lift_injective d.period_n hin, hnorthd, hipnative,
    oldw, holdw, hemb, hproj⟩

end
end TightVer401
