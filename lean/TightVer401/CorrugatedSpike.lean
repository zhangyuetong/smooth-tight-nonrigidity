import TightVer401.CorrugatedSpikeSetup
import TightVer401.CorrugatedSpikeNormal
import TightVer401.CorrugatedSeedBalancedOuter
import TightVer401.CorrugatedSeedBalancedSpatialNative

namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff Manifold Topology
set_option backward.isDefEq.respectTransparency false

/-- The explicit corrugated seed admits an arbitrarily L1-small scalar
holonomy correction with actual spatial and horizontal embeddings, both actual
visible pairs, and at most two arbitrarily short cell support arcs. -/
theorem corrugatedSeed_exists_balanced_embedded_speed {N : ℕ} (hN : 10000 ≤ N)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    let ell := corrugatedSeedArcCell (N : ℝ)
    let L := (N : ℝ) * ell
    letI : Fact (0 < ell) := ⟨corrugatedSeedArcCell_pos
      (by exact_mod_cast (show 1 < N by omega))⟩
    letI : Fact (0 < L) := ⟨mul_pos (by exact_mod_cast (show 0 < N by omega))
      (corrugatedSeedArcCell_pos (by exact_mod_cast (show 1 < N by omega)))⟩
    ∃ e : ℝ ≃ₜ ℝ, (e : ℝ → ℝ) = corrugatedSeedArcMap (N : ℝ) ∧
      ContDiff ℝ ∞ e.symm ∧
      (∀ r, HasDerivAt e.symm (corrugatedSeedSphericalSpeed (N : ℝ) (e.symm r))⁻¹ r) ∧
      ∃ a : ℝ → ℝ, ContDiff ℝ ∞ a ∧ Function.Periodic a ell ∧ (∀ r, 0 < a r) ∧
        (∫ r in 0..ell, ‖a r - corrugatedSeedInitialSpeed (N : ℝ) e.symm r‖) < η ∧
        (∫ r in 0..ell, a r * normalLoopTangent (corrugatedSeedSphere (N : ℝ) ∘ e.symm) r 2) = 0 ∧
        (∫ r in 0..L, a r • normalLoopTangent (corrugatedSeedSphere (N : ℝ) ∘ e.symm) r) = 0 ∧
        (∫ r in 0..ell, deriv (normalLoopCurvature (corrugatedSeedSphere (N : ℝ) ∘ e.symm)) r /
          Real.sqrt (a r)) = 0 ∧
        (∫ r in 0..L, deriv (normalLoopCurvature (corrugatedSeedSphere (N : ℝ) ∘ e.symm)) r /
          Real.sqrt (a r)) = 0 ∧
        ComplexVisiblePair (1 / 4) (corrugatedSeedBeta (N : ℝ) ∘ e.symm)
          (corrugatedSeedBalancedPartner (N : ℝ) e.symm ell a) ∧
        ComplexVisiblePair (4 / 5)
          (corrugatedReverseReflect (corrugatedSeedBalancedPartner (N : ℝ) e.symm ell a))
          (corrugatedReverseReflect (corrugatedSeedBeta (N : ℝ) ∘ e.symm)) ∧
        (∃ Cs : AddCircle L → Ambient, ∃ Ch : AddCircle L → ℂ,
          ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Ambient) ∞ Cs ∧ Topology.IsEmbedding Cs ∧
          (∀ q, Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Ambient) Cs q)) ∧
          ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ Ch ∧ Topology.IsEmbedding Ch ∧
          (∀ q, Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) Ch q)) ∧
          (∀ r, Cs (periodProjection L r) = corrugatedSeedBalancedSpatial (N : ℝ) e.symm ell a r) ∧
          (∀ r, Ch (periodProjection L r) = covariantSpeedCurve ell (corrugatedSeedRotation (N : ℝ))
            a (corrugatedSeedFrameHorizontal (N : ℝ) e.symm) r) ∧
          (∀ q, Ch q = corrugatedAmbientHorizontalCLM (Cs q))) ∧
        ∃ A B : AddCircle ell → ℝ,
          ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ A ∧ ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ B ∧
          (∀ r, A (periodProjection ell r) = a r) ∧
          (∀ r, B (periodProjection ell r) = corrugatedSeedInitialSpeed (N : ℝ) e.symm r) ∧
          ∃ n : ℕ, n ≤ 2 ∧ ∃ centers radii : Fin n → ℝ,
            (∀ j, 0 ≤ radii j) ∧ (∑ j, 2 * radii j) < ε ∧
            Function.support (fun q => A q - B q) ⊆
              ⋃ j, periodProjection ell '' Icc (centers j - radii j) (centers j + radii j) := by
  dsimp only
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNlarge : (10000 : ℝ) ≤ N := by exact_mod_cast hN
  have hNz : N ≠ 0 := by omega
  let ell := corrugatedSeedArcCell (N : ℝ)
  let L := (N : ℝ) * ell
  letI : Fact (0 < ell) := ⟨corrugatedSeedArcCell_pos hNr⟩
  letI : Fact (0 < L) := ⟨mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hNz))
    (corrugatedSeedArcCell_pos hNr)⟩
  obtain ⟨e, he, hψ, hi, hc⟩ := corrugatedSeed_exists_cell_arclength hNr
  obtain ⟨a, ha, haT, hapos, hsmall, hMcell, hMfull, hBcell, hBfull,
    _, hicov, hvis, hsupport⟩ := corrugatedSeed_spike_speed hN e he hψ hi hη hε
  have hnormal := corrugatedSeed_spike_normal (by omega : 2 ≤ N) e he hψ hi
  have hPL := (normalLoop_actual_periodic hnormal.2.1 hnormal.2.2.1).1
  have haL : Function.Periodic a L := haT.nat_mul N
  obtain ⟨Cs, hCs, hembCs, himmCs, hrepCs⟩ :=
    corrugatedSeedBalancedSpatial_native_embedding (ell := ell) hNr hψ hi ha hapos haL hPL hMfull hicov
  have hp := covariantSpeedCurve_periodic ha.continuous
    (corrugatedSeedFrameHorizontal_contDiff (N : ℝ) hψ).continuous haT
    (corrugatedSeedFrameHorizontal_cell hNr hψ hi hc) (corrugatedSeedRotation_ne_one hNr)
    N (corrugatedSeedRotation_pow hNz)
  have hs := covariantSpeedCurve_contDiff ell (corrugatedSeedRotation (N : ℝ)) ha
    (corrugatedSeedFrameHorizontal_contDiff (N : ℝ) hψ)
  obtain ⟨hCh, hembCh⟩ := periodicCurve_lift_embedding hs hp hicov
  have hd (r) : deriv (covariantSpeedCurve ell (corrugatedSeedRotation (N : ℝ)) a
      (corrugatedSeedFrameHorizontal (N : ℝ) e.symm)) r ≠ 0 := by
    rw [(covariantSpeedCurve_hasDerivAt ell (corrugatedSeedRotation (N : ℝ)) ha.continuous
      (corrugatedSeedFrameHorizontal_contDiff (N : ℝ) hψ).continuous r).deriv]
    exact smul_ne_zero (hapos r).ne' (corrugatedSeedFrameHorizontal_ne_zero hNr hψ hi r)
  have hcoords (q : AddCircle L) : hp.lift q = corrugatedAmbientHorizontalCLM (Cs q) := by
    obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective q
    change hp.lift (periodProjection L r) = corrugatedAmbientHorizontalCLM (Cs (periodProjection L r))
    rw [periodicLift_coe, hrepCs, corrugatedAmbientHorizontalCLM_apply,
      corrugatedSeedBalancedSpatial_horizontal (N : ℝ) ell hψ ha.continuous]
  exact ⟨e, he, hψ, hi, a, ha, haT, hapos, hsmall, hMcell, hMfull, hBcell, hBfull,
    corrugatedSeedBalancedPartner_outer_visible hψ ha hapos hvis,
    corrugatedSeedBalancedPartner_reflected_visible hNlarge hψ hi ha hapos,
    ⟨Cs, hp.lift, hCs, hembCs, himmCs, hCh, hembCh,
      periodicCurve_lift_mfderiv_injective hs hp hd, hrepCs, hp.lift_coe, hcoords⟩,
    hsupport⟩

end
end TightVer401
