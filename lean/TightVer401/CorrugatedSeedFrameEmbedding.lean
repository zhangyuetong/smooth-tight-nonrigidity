import TightVer401.CorrugatedSeedFrameBaseline
import TightVer401.CorrugatedSeedPartnerJordan
import TightVer401.NormalLoopEmbeddingArclength

namespace TightVer401
noncomputable section
open Set OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff

theorem corrugatedSeed_partner_arclength_injOn {N : ℕ} (hN : 10000 ≤ N)
    (e : ℝ ≃ₜ ℝ) (he : (e : ℝ → ℝ) = corrugatedSeedArcMap (N : ℝ)) :
    InjOn (corrugatedSeedPartner (N : ℝ) ∘ e.symm)
      (Ico 0 ((N : ℝ) * corrugatedSeedArcCell (N : ℝ))) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have h := normalLoop_arclength_reparameterized_injective
    (corrugatedSeedSphericalSpeed_contDiff hNr).continuous
    (corrugatedSeedSphericalSpeed_pos hNr) e he (corrugatedSeedPartner_injOn hN)
  rw [show rawPrimitive (corrugatedSeedSphericalSpeed (N : ℝ)) (2 * Real.pi) =
    (N : ℝ) * corrugatedSeedArcCell (N : ℝ) from
      corrugatedSeedArcMap_full_period (by omega : 2 ≤ N)] at h
  exact h

theorem corrugatedSeed_covariant_baseline_injOn {N : ℕ} (hN : 10000 ≤ N)
    (e : ℝ ≃ₜ ℝ) (he : (e : ℝ → ℝ) = corrugatedSeedArcMap (N : ℝ))
    (hψ : ContDiff ℝ ∞ e.symm) :
    InjOn (covariantSpeedCurve (corrugatedSeedArcCell (N : ℝ)) (corrugatedSeedRotation (N : ℝ))
      (corrugatedSeedInitialSpeed (N : ℝ) e.symm) (corrugatedSeedFrameHorizontal (N : ℝ) e.symm))
      (Ico 0 ((N : ℝ) * corrugatedSeedArcCell (N : ℝ))) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  intro s hs t ht hst
  rw [corrugatedSeed_covariant_baseline hNr hψ (corrugatedSeedArcInverse_cell hNr e he),
    corrugatedSeed_covariant_baseline hNr hψ (corrugatedSeedArcInverse_cell hNr e he)] at hst
  apply corrugatedSeed_partner_arclength_injOn hN e he hs ht
  exact mul_left_cancel₀ (neg_ne_zero.mpr Complex.I_ne_zero) hst

theorem corrugatedSeed_spatial_arclength_injOn {N : ℕ} (hN : 10000 ≤ N)
    (e : ℝ ≃ₜ ℝ) (he : (e : ℝ → ℝ) = corrugatedSeedArcMap (N : ℝ)) :
    InjOn (corrugatedSeedSpatial (N : ℝ) ∘ e.symm)
      (Ico 0 ((N : ℝ) * corrugatedSeedArcCell (N : ℝ))) := by
  intro s hs t ht hst
  apply corrugatedSeed_partner_arclength_injOn hN e he hs ht
  have h := congrArg corrugatedAmbientHorizontal hst
  change corrugatedAmbientHorizontal (corrugatedSeedSpatial (N : ℝ) (e.symm s)) =
    corrugatedAmbientHorizontal (corrugatedSeedSpatial (N : ℝ) (e.symm t)) at h
  rw [corrugatedSeedSpatial_horizontal, corrugatedSeedSpatial_horizontal] at h
  exact mul_left_cancel₀ (neg_ne_zero.mpr Complex.I_ne_zero) h

end
end TightVer401
