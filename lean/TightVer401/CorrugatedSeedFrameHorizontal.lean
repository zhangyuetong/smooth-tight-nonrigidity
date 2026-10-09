import TightVer401.CorrugatedSeedFrameFormula
import TightVer401.CorrugatedSeedCellArclength

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff

def corrugatedAmbientHorizontalCLM : Ambient →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 0) +
    Complex.I • (Complex.ofRealCLM.comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 1))

theorem corrugatedAmbientHorizontalCLM_apply (u : Ambient) :
    corrugatedAmbientHorizontalCLM u = corrugatedAmbientHorizontal u := by
  apply Complex.ext <;> simp [corrugatedAmbientHorizontalCLM, corrugatedAmbientHorizontal,
    Complex.mul_re, Complex.mul_im]

theorem corrugatedAmbientHorizontal_contDiff : ContDiff ℝ ∞ corrugatedAmbientHorizontal := by
  rw [show corrugatedAmbientHorizontal = corrugatedAmbientHorizontalCLM by
    funext u; exact (corrugatedAmbientHorizontalCLM_apply u).symm]
  exact corrugatedAmbientHorizontalCLM.contDiff

theorem corrugatedAmbientHorizontal_smul (a : ℝ) (u : Ambient) :
    corrugatedAmbientHorizontal (a • u) = a • corrugatedAmbientHorizontal u := by
  rw [← corrugatedAmbientHorizontalCLM_apply, ← corrugatedAmbientHorizontalCLM_apply, map_smul]

theorem corrugatedAmbientHorizontal_rotation (ξ : ℂ) (u : Ambient) :
    corrugatedAmbientHorizontal (corrugatedAmbientRotation ξ u) = ξ * corrugatedAmbientHorizontal u := by
  apply Complex.ext
  · rfl
  · exact add_comm _ _

theorem corrugatedAmbientHorizontal_hasDerivAt {f : ℝ → Ambient} {v : Ambient} {r : ℝ}
    (hf : HasDerivAt f v r) :
    HasDerivAt (fun s => corrugatedAmbientHorizontal (f s)) (corrugatedAmbientHorizontal v) r := by
  have h := corrugatedAmbientHorizontalCLM.hasFDerivAt.comp_hasDerivAt r hf
  have h' := h.congr_of_eventuallyEq (f₁ := fun s => corrugatedAmbientHorizontal (f s))
    (Filter.Eventually.of_forall (fun s => (corrugatedAmbientHorizontalCLM_apply (f s)).symm))
  exact (corrugatedAmbientHorizontalCLM_apply v) ▸ h'

theorem corrugatedNormalNumerator_horizontal (z v : ℂ) :
    corrugatedAmbientHorizontal (corrugatedNormalNumerator z v) = -Complex.I * v := by
  apply Complex.ext <;> simp [corrugatedAmbientHorizontal, corrugatedNormalNumerator,
    Complex.mul_re, Complex.mul_im]

theorem corrugatedSeedFrame_horizontal {N : ℝ} {ψ : ℝ → ℝ}
    (hψ : Differentiable ℝ ψ) (r : ℝ) :
    corrugatedAmbientHorizontal (normalLoopTangent (corrugatedSeedSphere N ∘ ψ) r) =
      (corrugatedSeedSphereScale N (ψ r))^2 • (-Complex.I * deriv (corrugatedSeedBeta N ∘ ψ) r) := by
  rw [corrugatedSeedFrame_tangent hψ, corrugatedAmbientHorizontal_smul,
    corrugatedNormalNumerator_horizontal]

theorem corrugatedSeedFrame_horizontal_ne_zero {N : ℝ} (hN : 1 < N) {ψ : ℝ → ℝ}
    (hψ : Differentiable ℝ ψ)
    (hi : ∀ r, HasDerivAt ψ (corrugatedSeedSphericalSpeed N (ψ r))⁻¹ r) (r : ℝ) :
    corrugatedAmbientHorizontal (normalLoopTangent (corrugatedSeedSphere N ∘ ψ) r) ≠ 0 := by
  rw [corrugatedSeedFrame_horizontal hψ, corrugatedComplex_comp_deriv
    ((corrugatedSeedBeta_contDiff N).differentiable (by simp)) hψ,
    (hi r).deriv, corrugatedSeedBeta_deriv (ne_of_gt (by linarith : 0 < N))]
  apply smul_ne_zero (pow_ne_zero 2 (ne_of_gt (corrugatedSeedSphereScale_pos N _)))
  apply mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
  exact smul_ne_zero (inv_ne_zero (ne_of_gt (corrugatedSeedSphericalSpeed_pos hN _)))
    (corrugatedSeedBetaVelocity_ne_zero hN _)

end
end TightVer401
