import TightVer401.PeriodicRuledFrame
import TightVer401.BandProjectionDifferential
import TightVer401.CoordinateBendingPullback

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped Manifold ContDiff
set_option backward.isDefEq.respectTransparency false

def IsBandBending {L b : ℝ} [Fact (0 < L)]
    (X Y : AddCircle L × Set.Ioo (0 : ℝ) b → Ambient) : Prop :=
  ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Ambient) ∞ Y ∧
  ∀ p : AddCircle L × Set.Ioo (0 : ℝ) b, ∀ v w : ℝ × ℝ,
    inner ℝ (bandDifferential X p v) (bandDifferential Y p w) +
    inner ℝ (bandDifferential Y p v) (bandDifferential X p w) = 0

theorem periodic_ruled_profile_isBandBending {L b : ℝ} [Fact (0 < L)]
    (d : PeriodicRuledFrame L) {W F : ℝ → ℝ}
    (hWL : Function.Periodic W L) (hWs : ContDiff ℝ ∞ W)
    (hW : ∀ s, HasDerivAt W (ruledPeriodCoefficient d.k d.τ s) s)
    (hF : ContDiff ℝ ∞ F) :
    IsBandBending (d.bandMap (b := b)) (d.profile (F := F) hWL) := by
  have hYs := d.profile_contMDiff hWL hWs hF (b := b)
  refine ⟨hYs, band_zero_strain_descends d.bandMap_contMDiff hYs ?_⟩
  have hXlift : d.bandMap (b := b) ∘ bandProjection L b =
      ruledMap d.γ d.E ∘ realBandCoordinates b := rfl
  have hYlift : d.profile (b := b) (F := F) hWL ∘ bandProjection L b =
      ruledProfileField d.k d.τ (ruledRho d.τ) W F d.T d.n ∘ realBandCoordinates b := by
    funext p
    exact periodic_bandProfile_real_lift d.period_k d.period_τ (ruledRho_periodic d.period_τ)
      hWL d.period_T d.period_n p.1 p.2
  have hXc : ContDiff ℝ ∞ (ruledMap d.γ d.E) :=
    (d.smooth_γ.comp (contDiff_apply ℝ ℝ 0)).add
      ((contDiff_apply ℝ ℝ 1).smul (d.smooth_E.comp (contDiff_apply ℝ ℝ 0)))
  have hYc := ruled_profile_smoothOn d.smooth_k d.smooth_τ
    (ruledRho_contDiff d.smooth_τ d.torsion_ne_zero) hWs hF d.smooth_T d.smooth_n
    (fun s => ne_of_gt (ruledRho_pos (d.torsion_ne_zero s)))
  intro p v w
  rw [hXlift, hYlift]
  have hu : (realBandCoordinates b p) 1 ≠ 0 := ne_of_gt p.2.property.1
  apply realBand_zero_strain_pullback p (hXc.differentiable (by simp) _)
    (((hYc _ hu).contDiffAt
      ((isOpen_ne_fun (continuous_apply 1) continuous_const).mem_nhds hu)).differentiableAt (by simp))
  exact ruled_actual_profile_zero_strain d.deriv_γ d.deriv_E d.deriv_T d.deriv_n
    d.smooth_k d.smooth_τ d.torsion_ne_zero hW hF d.orthonormal hu

end
end TightVer401
