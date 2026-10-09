import TightVer401.CorrugatedSeedCellArclength

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff RealInnerProductSpace

theorem corrugatedSeed_exists_cell_arclength {N : ℝ} (hN : 1 < N) :
    ∃ e : ℝ ≃ₜ ℝ, (e : ℝ → ℝ) = corrugatedSeedArcMap N ∧
      ContDiff ℝ ∞ e.symm ∧
      (∀ r, HasDerivAt e.symm (corrugatedSeedSphericalSpeed N (e.symm r))⁻¹ r) ∧
      (∀ r, e.symm (r + corrugatedSeedArcCell N) = e.symm r + corrugatedSeedCell N) := by
  exact normalLoop_exists_global_arclength_inverse
    (corrugatedSeedSphericalSpeed_contDiff hN) (corrugatedSeedSphericalSpeed_pos hN)
    (corrugatedSeedSphericalSpeed_periodic (ne_of_gt (by linarith : 0 < N)))
    (by unfold corrugatedSeedCell; positivity)

theorem corrugatedSeed_arclength_unit_frame {N : ℝ} (hN : 1 < N)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hi : ∀ r, HasDerivAt ψ (corrugatedSeedSphericalSpeed N (ψ r))⁻¹ r) :
    (∀ r, inner ℝ (corrugatedSeedSphere N (ψ r)) (corrugatedSeedSphere N (ψ r)) = 1) ∧
      (∀ r, inner ℝ (deriv (corrugatedSeedSphere N ∘ ψ) r)
        (deriv (corrugatedSeedSphere N ∘ ψ) r) = 1) := by
  constructor
  · intro r
    rw [real_inner_self_eq_norm_sq, corrugatedSeedSphere_unit, one_pow]
  · intro r
    rw [real_inner_self_eq_norm_sq, sphericalCurve_comp_deriv
      ((corrugatedSeedSphere_contDiff N).differentiable (by simp)) (hψ.differentiable (by simp)),
      (hi r).deriv, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (corrugatedSeedSphericalSpeed_pos hN _))]
    change ((corrugatedSeedSphericalSpeed N (ψ r))⁻¹ * corrugatedSeedSphericalSpeed N (ψ r))^2 = 1
    rw [inv_mul_cancel₀ (ne_of_gt (corrugatedSeedSphericalSpeed_pos hN _)), one_pow]

theorem corrugatedSeed_actual_spherical_frame {N : ℝ} (hN : 1 < N)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hi : ∀ r, HasDerivAt ψ (corrugatedSeedSphericalSpeed N (ψ r))⁻¹ r) (r : ℝ) :
    IsOrthonormalFrame (normalLoopTangent (corrugatedSeedSphere N ∘ ψ) r)
      (deriv (corrugatedSeedSphere N ∘ ψ) r) (corrugatedSeedSphere N (ψ r)) ∧
      HasDerivAt (normalLoopTangent (corrugatedSeedSphere N ∘ ψ))
        (normalLoopCurvature (corrugatedSeedSphere N ∘ ψ) r •
          deriv (corrugatedSeedSphere N ∘ ψ) r) r ∧
      deriv (deriv (corrugatedSeedSphere N ∘ ψ)) r =
        -corrugatedSeedSphere N (ψ r) - normalLoopCurvature (corrugatedSeedSphere N ∘ ψ) r •
          normalLoopTangent (corrugatedSeedSphere N ∘ ψ) r := by
  have hf := corrugatedSeed_arclength_unit_frame hN hψ hi
  exact normalLoop_actual_frame ((corrugatedSeedSphere_contDiff N).comp hψ) hf.1 hf.2 r

end
end TightVer401
