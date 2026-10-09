import TightVer401.CorrugatedSeedFrameBaseline

namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff

def corrugatedSeedBalancedSpatial (N : ℝ) (ψ : ℝ → ℝ) (ell : ℝ) (a : ℝ → ℝ) (r : ℝ) : Ambient :=
  speedCurve a (normalLoopTangent (corrugatedSeedSphere N ∘ ψ)) r +
    corrugatedHorizontal (speedCurve a (corrugatedSeedFrameHorizontal N ψ) ell /
      (corrugatedSeedRotation N - 1))

theorem corrugatedSeedBalancedSpatial_contDiff (N ell : ℝ) {ψ a : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (corrugatedSeedBalancedSpatial N ψ ell a) :=
  (rawPrimitive_contDiff (ha.smul
    (normalLoop_actual_smooth ((corrugatedSeedSphere_contDiff N).comp hψ)).1)).add contDiff_const

theorem corrugatedSeedBalancedSpatial_hasDerivAt (N ell : ℝ) {ψ a : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (ha : Continuous a) (r : ℝ) :
    HasDerivAt (corrugatedSeedBalancedSpatial N ψ ell a)
      (a r • normalLoopTangent (corrugatedSeedSphere N ∘ ψ) r) r :=
  (rawPrimitive_hasDerivAt (ha.smul
    (normalLoop_actual_smooth ((corrugatedSeedSphere_contDiff N).comp hψ)).1.continuous) r).add_const _

theorem corrugatedSeedBalancedSpatial_horizontal (N ell : ℝ) {ψ a : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (ha : Continuous a) (r : ℝ) :
    corrugatedAmbientHorizontal (corrugatedSeedBalancedSpatial N ψ ell a r) =
      covariantSpeedCurve ell (corrugatedSeedRotation N) a (corrugatedSeedFrameHorizontal N ψ) r := by
  have hP := (normalLoop_actual_smooth ((corrugatedSeedSphere_contDiff N).comp hψ)).1.continuous
  have he := corrugatedAmbientHorizontalCLM.intervalIntegral_comp_comm
    ((ha.smul hP).intervalIntegrable (μ := volume) 0 r)
  have hi : corrugatedAmbientHorizontal (speedCurve a (normalLoopTangent (corrugatedSeedSphere N ∘ ψ)) r) =
      speedCurve a (corrugatedSeedFrameHorizontal N ψ) r := by
    simpa only [speedCurve, rawPrimitive, Pi.smul_apply', corrugatedAmbientHorizontalCLM_apply,
      corrugatedAmbientHorizontal_smul, corrugatedSeedFrameHorizontal] using he.symm
  rw [← corrugatedAmbientHorizontalCLM_apply]
  unfold corrugatedSeedBalancedSpatial
  rw [map_add, corrugatedAmbientHorizontalCLM_apply, corrugatedAmbientHorizontalCLM_apply, hi]
  have hz (z : ℂ) : corrugatedAmbientHorizontal (corrugatedHorizontal z) = z := by
    apply Complex.ext <;> rfl
  rw [hz]
  exact add_comm _ _

theorem corrugatedSeedBalancedSpatial_vertical (N ell : ℝ) {ψ a : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (ha : Continuous a) (r : ℝ) :
    corrugatedSeedBalancedSpatial N ψ ell a r 2 =
      ∫ s in 0..r, a s * normalLoopTangent (corrugatedSeedSphere N ∘ ψ) s 2 := by
  have hP := (normalLoop_actual_smooth ((corrugatedSeedSphere_contDiff N).comp hψ)).1.continuous
  have he := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 2).intervalIntegral_comp_comm
    ((ha.smul hP).intervalIntegrable (μ := volume) 0 r)
  change (∫ s in 0..r, a s * normalLoopTangent (corrugatedSeedSphere N ∘ ψ) s 2) =
    speedCurve a (normalLoopTangent (corrugatedSeedSphere N ∘ ψ)) r 2 at he
  change speedCurve a (normalLoopTangent (corrugatedSeedSphere N ∘ ψ)) r 2 + 0 = _
  rw [add_zero, he]

theorem corrugatedSeedBalancedSpatial_injOn {N ell : ℝ} {ψ a : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (ha : Continuous a) {S : Set ℝ}
    (hi : InjOn (covariantSpeedCurve ell (corrugatedSeedRotation N) a
      (corrugatedSeedFrameHorizontal N ψ)) S) :
    InjOn (corrugatedSeedBalancedSpatial N ψ ell a) S := by
  intro s hs t ht hst
  apply hi hs ht
  have h := congrArg corrugatedAmbientHorizontal hst
  simpa only [corrugatedSeedBalancedSpatial_horizontal N ell hψ ha] using h

end
end TightVer401
