import TightVer401.CorrugatedSeedBalancedSpatial

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff

theorem corrugatedAmbientHorizontal_vertical_injective : Function.Injective
    (fun v : Ambient => (corrugatedAmbientHorizontalCLM v,
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 2) v)) := by
  intro u v h
  have hh := congrArg Prod.fst h
  change corrugatedAmbientHorizontalCLM u = corrugatedAmbientHorizontalCLM v at hh
  rw [corrugatedAmbientHorizontalCLM_apply, corrugatedAmbientHorizontalCLM_apply] at hh
  have h0 := congrArg Complex.re hh
  have h1 := congrArg Complex.im hh
  have h2 := congrArg Prod.snd h
  ext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

theorem corrugatedSeedBalancedSpatial_initial {N : ℝ} (hN : 1 < N)
    {ψ : ℝ → ℝ} {ell : ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hcell : ∀ r, ψ (r + ell) = ψ r + corrugatedSeedCell N) (hz : ψ 0 = 0) :
    corrugatedSeedBalancedSpatial N ψ ell (corrugatedSeedInitialSpeed N ψ) =
      corrugatedSeedSpatial N ∘ ψ := by
  funext r
  apply corrugatedAmbientHorizontal_vertical_injective
  apply Prod.ext
  · simp only [corrugatedAmbientHorizontalCLM_apply, Function.comp_apply]
    rw [corrugatedSeedBalancedSpatial_horizontal N ell hψ
      (corrugatedSeedInitialSpeed_contDiff N hψ).continuous,
      corrugatedSeed_covariant_baseline hN hψ hcell, corrugatedSeedSpatial_horizontal]
  · change corrugatedSeedBalancedSpatial N ψ ell (corrugatedSeedInitialSpeed N ψ) r 2 =
      corrugatedSeedSpatial N (ψ r) 2
    rw [corrugatedSeedBalancedSpatial_vertical N ell hψ
      (corrugatedSeedInitialSpeed_contDiff N hψ).continuous]
    have hP := (normalLoop_actual_smooth ((corrugatedSeedSphere_contDiff N).comp hψ)).1
    have hd (s : ℝ) : HasDerivAt (fun t => corrugatedSeedSpatial N (ψ t) 2)
        (corrugatedSeedInitialSpeed N ψ s * normalLoopTangent (corrugatedSeedSphere N ∘ ψ) s 2) s :=
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 2).hasFDerivAt.comp_hasDerivAt s
        (corrugatedSeedSpatial_frame_hasDerivAt hN hψ s)
    have hp : Continuous (fun s => normalLoopTangent (corrugatedSeedSphere N ∘ ψ) s 2) :=
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 2).continuous.comp hP.continuous
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
      (((corrugatedSeedInitialSpeed_contDiff N hψ).continuous.mul hp).intervalIntegrable 0 r)]
    have hzero : corrugatedSeedSpatial N (ψ 0) 2 = 0 := by
      rw [hz]
      simp [corrugatedSeedSpatial, corrugatedSeedVertical, rawPrimitive]
    rw [hzero, sub_zero]

end
end TightVer401
