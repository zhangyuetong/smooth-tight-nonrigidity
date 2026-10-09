import TightVer401.CorrugatedSeedFrameHorizontal
import TightVer401.CorrugatedSeedFrameCell
import TightVer401.CorrugatedSeedScalarClosure
import TightVer401.CovariantSpeedPrimitive

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff

def corrugatedSeedFrameHorizontal (N : ℝ) (ψ : ℝ → ℝ) (r : ℝ) : ℂ :=
  corrugatedAmbientHorizontal (normalLoopTangent (corrugatedSeedSphere N ∘ ψ) r)

theorem corrugatedSeedFrameHorizontal_contDiff (N : ℝ) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) : ContDiff ℝ ∞ (corrugatedSeedFrameHorizontal N ψ) :=
  corrugatedAmbientHorizontal_contDiff.comp
    (normalLoop_actual_smooth ((corrugatedSeedSphere_contDiff N).comp hψ)).1

theorem corrugatedSeedFrameHorizontal_cell {N : ℝ} (hN : 1 < N)
    {ψ : ℝ → ℝ} {ell : ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hi : ∀ r, HasDerivAt ψ (corrugatedSeedSphericalSpeed N (ψ r))⁻¹ r)
    (hcell : ∀ r, ψ (r + ell) = ψ r + corrugatedSeedCell N) (r : ℝ) :
    corrugatedSeedFrameHorizontal N ψ (r + ell) =
      corrugatedSeedRotation N * corrugatedSeedFrameHorizontal N ψ r := by
  unfold corrugatedSeedFrameHorizontal
  rw [corrugatedSeedFrame_tangent_cell hN hψ hi hcell,
    corrugatedAmbientHorizontal_rotation]

theorem corrugatedSeedFrameHorizontal_ne_zero {N : ℝ} (hN : 1 < N)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hi : ∀ r, HasDerivAt ψ (corrugatedSeedSphericalSpeed N (ψ r))⁻¹ r) (r : ℝ) :
    corrugatedSeedFrameHorizontal N ψ r ≠ 0 :=
  corrugatedSeedFrame_horizontal_ne_zero hN (hψ.differentiable (by simp)) hi r

theorem corrugatedSeedSpatial_horizontal_frame_hasDerivAt {N : ℝ} (hN : 1 < N)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (r : ℝ) :
    HasDerivAt (fun s => corrugatedAmbientHorizontal (corrugatedSeedSpatial N (ψ s)))
      (corrugatedSeedInitialSpeed N ψ r • corrugatedSeedFrameHorizontal N ψ r) r := by
  have h := corrugatedAmbientHorizontal_hasDerivAt
    (corrugatedSeedSpatial_frame_hasDerivAt hN hψ r)
  rw [corrugatedAmbientHorizontal_smul] at h
  exact h

theorem corrugatedSeed_initial_horizontal_primitive {N : ℝ} (hN : 1 < N)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (r : ℝ) :
    speedCurve (corrugatedSeedInitialSpeed N ψ) (corrugatedSeedFrameHorizontal N ψ) r =
      corrugatedAmbientHorizontal (corrugatedSeedSpatial N (ψ r)) -
        corrugatedAmbientHorizontal (corrugatedSeedSpatial N (ψ 0)) := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => corrugatedSeedSpatial_horizontal_frame_hasDerivAt hN hψ s)
    (((corrugatedSeedInitialSpeed_contDiff N hψ).continuous.smul
      (corrugatedSeedFrameHorizontal_contDiff N hψ).continuous).intervalIntegrable 0 r)

/-- The covariant starting point is exactly the seed's actual spatial horizontal projection. -/
theorem corrugatedSeed_covariant_baseline {N : ℝ} (hN : 1 < N)
    {ψ : ℝ → ℝ} {ell : ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hcell : ∀ r, ψ (r + ell) = ψ r + corrugatedSeedCell N) (r : ℝ) :
    covariantSpeedCurve ell (corrugatedSeedRotation N)
      (corrugatedSeedInitialSpeed N ψ) (corrugatedSeedFrameHorizontal N ψ) r =
      -Complex.I * corrugatedSeedPartner N (ψ r) := by
  have hc : ψ ell = ψ 0 + corrugatedSeedCell N := by
    simpa only [zero_add] using hcell 0
  have hf : corrugatedAmbientHorizontal (corrugatedSeedSpatial N (ψ ell)) =
      corrugatedSeedRotation N * corrugatedAmbientHorizontal (corrugatedSeedSpatial N (ψ 0)) := by
    rw [hc, corrugatedSeedSpatial_cell hN, corrugatedAmbientHorizontal_rotation]
  have hz := sub_ne_zero.mpr (corrugatedSeedRotation_ne_one hN)
  unfold covariantSpeedCurve
  rw [corrugatedSeed_initial_horizontal_primitive hN hψ ell,
    corrugatedSeed_initial_horizontal_primitive hN hψ r, hf]
  rw [← corrugatedSeedSpatial_horizontal N (ψ r)]
  field_simp
  ring

end
end TightVer401
