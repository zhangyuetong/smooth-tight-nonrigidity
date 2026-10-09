import TightVer401.CorrugatedSeedFrameFormula
import TightVer401.CorrugatedSeedCellCurvature

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff

theorem corrugatedSeedSpatial_frame_hasDerivAt {N : ℝ} (hN : 1 < N) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (r : ℝ) :
    HasDerivAt (corrugatedSeedSpatial N ∘ ψ)
      (corrugatedSeedInitialSpeed N ψ r • normalLoopTangent (corrugatedSeedSphere N ∘ ψ) r) r := by
  have h := (((corrugatedSeedSpatial_contDiff N).comp hψ).differentiable (by simp) r).hasDerivAt
  rw [corrugatedSeedSpatial_frame_deriv hN (hψ.differentiable (by simp))] at h
  exact h

theorem corrugatedSeed_initial_scalar_moment {N : ℝ} (hN : 1 < N)
    {ψ : ℝ → ℝ} {ell : ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hcell : ∀ r, ψ (r + ell) = ψ r + corrugatedSeedCell N) :
    (∫ r in 0..ell, corrugatedSeedInitialSpeed N ψ r *
      normalLoopTangent (corrugatedSeedSphere N ∘ ψ) r 2) = 0 := by
  let f : ℝ → ℝ := fun r => corrugatedSeedSpatial N (ψ r) 2
  let p : ℝ → ℝ := fun r => normalLoopTangent (corrugatedSeedSphere N ∘ ψ) r 2
  have hP := (normalLoop_actual_smooth ((corrugatedSeedSphere_contDiff N).comp hψ)).1
  have hp : Continuous p :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 2).continuous.comp hP.continuous
  have hd (r : ℝ) : HasDerivAt f (corrugatedSeedInitialSpeed N ψ r * p r) r :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 2).hasFDerivAt.comp_hasDerivAt r
      (corrugatedSeedSpatial_frame_hasDerivAt hN hψ r)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r)
    (((corrugatedSeedInitialSpeed_contDiff N hψ).continuous.mul hp).intervalIntegrable 0 ell)
  change (∫ r in 0..ell, corrugatedSeedInitialSpeed N ψ r * p r) = 0
  rw [hi]
  have hc : ψ ell = ψ 0 + corrugatedSeedCell N := by simpa only [zero_add] using hcell 0
  change corrugatedSeedVertical N (ψ ell) - corrugatedSeedVertical N (ψ 0) = 0
  rw [hc, corrugatedSeedVertical_periodic hN (ψ 0), sub_self]

end
end TightVer401
