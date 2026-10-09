import TightVer401.CorrugatedSeedFrameFormula
import TightVer401.CorrugatedSeedCellCurvature

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff

theorem corrugatedAmbientRotation_smul (ξ : ℂ) (a : ℝ) (u : Ambient) :
    corrugatedAmbientRotation ξ (a • u) = a • corrugatedAmbientRotation ξ u := by
  ext i
  fin_cases i <;> simp [corrugatedAmbientRotation] <;> ring

theorem corrugatedNormalNumerator_rotate (θ : ℝ) (z v : ℂ) :
    corrugatedNormalNumerator (Complex.exp ((θ : ℂ) * Complex.I) * z)
      (Complex.exp ((θ : ℂ) * Complex.I) * v) =
      corrugatedAmbientRotation (Complex.exp ((θ : ℂ) * Complex.I)) (corrugatedNormalNumerator z v) := by
  ext i
  fin_cases i
  · simp [corrugatedNormalNumerator, corrugatedAmbientRotation, Complex.mul_im]
  · simp [corrugatedNormalNumerator, corrugatedAmbientRotation, Complex.mul_re]
    ring
  · change -corrugatedSeedPlaneDet (Complex.exp ((θ : ℂ) * Complex.I) * z)
      (Complex.exp ((θ : ℂ) * Complex.I) * v) = -corrugatedSeedPlaneDet z v
    rw [corrugatedSeedPlaneDet_rotate]

theorem corrugatedSeedSphere_tangent_cell {N : ℝ} (hN : N ≠ 0) (t : ℝ) :
    normalLoopTangent (corrugatedSeedSphere N) (t + corrugatedSeedCell N) =
      corrugatedAmbientRotation (corrugatedSeedRotation N) (normalLoopTangent (corrugatedSeedSphere N) t) := by
  rw [corrugatedSeedSphere_tangent, corrugatedSeedSphere_tangent,
    corrugatedSeedSphereScale_periodic hN t, corrugatedSeedBeta_cell hN,
    corrugated_complex_covariant_deriv (corrugatedSeedBeta_contDiff N) (corrugatedSeedBeta_cell hN) t]
  have hc : corrugatedNormalNumerator (corrugatedSeedRotation N * corrugatedSeedBeta N t)
      (corrugatedSeedRotation N * deriv (corrugatedSeedBeta N) t) =
      corrugatedAmbientRotation (corrugatedSeedRotation N)
        (corrugatedNormalNumerator (corrugatedSeedBeta N t) (deriv (corrugatedSeedBeta N) t)) :=
    corrugatedNormalNumerator_rotate _ _ _
  rw [hc, corrugatedAmbientRotation_smul]

theorem corrugatedSeedFrame_tangent_cell {N : ℝ} (hN : 1 < N) {ψ : ℝ → ℝ} {ell : ℝ}
    (hψ : ContDiff ℝ ∞ ψ)
    (hi : ∀ r, HasDerivAt ψ (corrugatedSeedSphericalSpeed N (ψ r))⁻¹ r)
    (hcell : ∀ r, ψ (r + ell) = ψ r + corrugatedSeedCell N) (r : ℝ) :
    normalLoopTangent (corrugatedSeedSphere N ∘ ψ) (r + ell) =
      corrugatedAmbientRotation (corrugatedSeedRotation N) (normalLoopTangent (corrugatedSeedSphere N ∘ ψ) r) := by
  have hNz : N ≠ 0 := ne_of_gt (by linarith)
  rw [normalLoopTangent_comp ((corrugatedSeedSphere_contDiff N).differentiable (by simp))
    (hψ.differentiable (by simp)),
    normalLoopTangent_comp ((corrugatedSeedSphere_contDiff N).differentiable (by simp))
      (hψ.differentiable (by simp)),
    (hi (r + ell)).deriv, (hi r).deriv, hcell r,
    corrugatedSeedSphericalSpeed_periodic hNz (ψ r), corrugatedSeedSphere_tangent_cell hNz,
    corrugatedAmbientRotation_smul]

theorem corrugatedSeedInitialSpeed_periodic {N : ℝ} (hN : N ≠ 0) {ψ : ℝ → ℝ} {ell : ℝ}
    (hcell : ∀ r, ψ (r + ell) = ψ r + corrugatedSeedCell N) :
    Function.Periodic (corrugatedSeedInitialSpeed N ψ) ell := by
  intro r
  unfold corrugatedSeedInitialSpeed
  have hm : corrugatedSeedMultiplier (corrugatedSeedRoot N) N (ψ r + corrugatedSeedCell N) =
      corrugatedSeedMultiplier (corrugatedSeedRoot N) N (ψ r) :=
    corrugatedSeedMultiplier_periodic _ hN (ψ r)
  rw [hcell r, hm,
    corrugatedSeedBeta_cell hN, corrugatedComplexCoord_weight,
    corrugatedComplexCoord_weight, norm_mul]
  simp only [corrugatedSeedRotation, Complex.norm_exp_ofReal_mul_I, one_mul]

theorem corrugatedSeedSpatial_cell {N : ℝ} (hN : 1 < N) (t : ℝ) :
    corrugatedSeedSpatial N (t + corrugatedSeedCell N) =
      corrugatedAmbientRotation (corrugatedSeedRotation N) (corrugatedSeedSpatial N t) := by
  have hh : -Complex.I * corrugatedSeedPartner N (t + corrugatedSeedCell N) =
      corrugatedSeedRotation N * (-Complex.I * corrugatedSeedPartner N t) := by
    rw [corrugatedSeedPartner_cell hN]
    ring
  ext i
  fin_cases i
  · have h := congrArg Complex.re hh
    change (-Complex.I * corrugatedSeedPartner N (t + corrugatedSeedCell N)).re =
      (corrugatedSeedRotation N).re * (-Complex.I * corrugatedSeedPartner N t).re -
        (corrugatedSeedRotation N).im * (-Complex.I * corrugatedSeedPartner N t).im
    simpa only [Complex.mul_re] using h
  · have h := congrArg Complex.im hh
    change (-Complex.I * corrugatedSeedPartner N (t + corrugatedSeedCell N)).im =
      (corrugatedSeedRotation N).im * (-Complex.I * corrugatedSeedPartner N t).re +
        (corrugatedSeedRotation N).re * (-Complex.I * corrugatedSeedPartner N t).im
    change (-Complex.I * corrugatedSeedPartner N (t + corrugatedSeedCell N)).im =
      (corrugatedSeedRotation N).re * (-Complex.I * corrugatedSeedPartner N t).im +
        (corrugatedSeedRotation N).im * (-Complex.I * corrugatedSeedPartner N t).re at h
    exact h.trans (add_comm _ _)
  · exact corrugatedSeedVertical_periodic hN t

theorem corrugatedSeedFrame_vertical_periodic {N : ℝ} (hN : 1 < N)
    {ψ : ℝ → ℝ} {ell : ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hi : ∀ r, HasDerivAt ψ (corrugatedSeedSphericalSpeed N (ψ r))⁻¹ r)
    (hcell : ∀ r, ψ (r + ell) = ψ r + corrugatedSeedCell N) :
    Function.Periodic (fun r => normalLoopTangent (corrugatedSeedSphere N ∘ ψ) r 2) ell := by
  intro r
  change normalLoopTangent (corrugatedSeedSphere N ∘ ψ) (r + ell) 2 =
    normalLoopTangent (corrugatedSeedSphere N ∘ ψ) r 2
  rw [corrugatedSeedFrame_tangent_cell hN hψ hi hcell r]
  rfl

end
end TightVer401
