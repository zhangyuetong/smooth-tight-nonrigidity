import TightVer401.CorrugatedSeedFrameBaseline
import TightVer401.CorrugatedSeedVisiblePairs

namespace TightVer401
noncomputable section
open scoped ContDiff RealInnerProductSpace ComplexConjugate

theorem ComplexVisiblePair.comp {R : ℝ} {p δ : ℝ → ℂ} {ψ : ℝ → ℝ}
    (hv : ComplexVisiblePair R p δ) (hp : Differentiable ℝ p) (hδ : Differentiable ℝ δ)
    (hψ : Differentiable ℝ ψ) (hpos : ∀ r, 0 < deriv ψ r) :
    ComplexVisiblePair R (p ∘ ψ) (δ ∘ ψ) := by
  intro r
  refine ⟨(hv (ψ r)).1, ?_, ?_⟩
  · rw [corrugatedComplex_comp_deriv hp hψ, real_inner_smul_left]
    exact mul_pos (hpos r) (hv (ψ r)).2.1
  · rw [corrugatedComplex_comp_deriv hδ hψ, real_inner_smul_left]
    exact mul_pos (hpos r) (hv (ψ r)).2.2

theorem corrugated_complex_inner_negI (z w : ℂ) :
    inner ℝ (-Complex.I * z) (-Complex.I * w) = inner ℝ z w := by
  simp only [corrugated_complex_inner, Complex.mul_re, Complex.mul_im,
    Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
  ring

theorem corrugatedSeedFrame_outer_visible {N : ℝ} (hN : 10000 ≤ N)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hi : ∀ r, HasDerivAt ψ (corrugatedSeedSphericalSpeed N (ψ r))⁻¹ r) :
    ComplexVisiblePair (1 / 4) (corrugatedSeedBeta N ∘ ψ) (corrugatedSeedPartner N ∘ ψ) := by
  apply (corrugatedSeed_outer_visible hN).comp
    ((corrugatedSeedBeta_contDiff N).differentiable (by simp))
    ((corrugatedSeedPartner_contDiff N).differentiable (by simp)) (hψ.differentiable (by simp))
  intro r
  rw [(hi r).deriv]
  exact inv_pos.mpr (corrugatedSeedSphericalSpeed_pos (by linarith : 1 < N) _)

theorem corrugatedSeedFrame_reflected_visible {N : ℝ} (hN : 10000 ≤ N)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hi : ∀ r, HasDerivAt ψ (corrugatedSeedSphericalSpeed N (ψ r))⁻¹ r) :
    ComplexVisiblePair (4 / 5) (corrugatedReverseReflect (corrugatedSeedPartner N ∘ ψ))
      (corrugatedReverseReflect (corrugatedSeedBeta N ∘ ψ)) := by
  intro r
  have hNr : 1 < N := by linarith
  have hpos : 0 < deriv ψ (-r) := by
    rw [(hi (-r)).deriv]
    exact inv_pos.mpr (corrugatedSeedSphericalSpeed_pos hNr _)
  have hp := corrugatedReverseReflect_hasDerivAt
    (((corrugatedSeedPartner_contDiff N).comp hψ).differentiable (by simp) (-r)).hasDerivAt
  have hb := corrugatedReverseReflect_hasDerivAt
    (((corrugatedSeedBeta_contDiff N).comp hψ).differentiable (by simp) (-r)).hasDerivAt
  refine ⟨?_, ?_, ?_⟩
  · simp only [corrugatedReverseReflect, Function.comp_apply, Complex.norm_conj]
    linarith [corrugatedSeedBeta_radius_lower hN (ψ (-r))]
  · rw [hp.deriv]
    change 0 < inner ℝ (-conj (deriv (corrugatedSeedPartner N ∘ ψ) (-r)))
      (corrugatedVisibilityDirection (4 / 5) (conj (corrugatedSeedBeta N (ψ (-r)))))
    rw [corrugated_reflection_inner, corrugatedComplex_comp_deriv
      ((corrugatedSeedPartner_contDiff N).differentiable (by simp)) (hψ.differentiable (by simp)),
      corrugatedSeedPartner_deriv hNr, real_inner_smul_left, real_inner_smul_left]
    exact mul_pos hpos (mul_pos (corrugatedSeedMultiplier_pos _ _ _)
      (corrugatedSeed_inner_velocity_visibility hN _))
  · rw [hb.deriv]
    change 0 < inner ℝ (-conj (deriv (corrugatedSeedBeta N ∘ ψ) (-r)))
      (corrugatedVisibilityDirection (4 / 5) (conj (corrugatedSeedBeta N (ψ (-r)))))
    rw [corrugated_reflection_inner, corrugatedComplex_comp_deriv
      ((corrugatedSeedBeta_contDiff N).differentiable (by simp)) (hψ.differentiable (by simp)),
      real_inner_smul_left]
    exact mul_pos hpos (corrugatedSeed_inner_velocity_visibility hN _)

theorem corrugatedSeed_covariant_baseline_visibility {N : ℝ} (hN : 10000 ≤ N)
    {ψ : ℝ → ℝ} {ell : ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hi : ∀ r, HasDerivAt ψ (corrugatedSeedSphericalSpeed N (ψ r))⁻¹ r)
    (hcell : ∀ r, ψ (r + ell) = ψ r + corrugatedSeedCell N) (r : ℝ) :
    (1 / 4 : ℝ) < ‖covariantSpeedCurve ell (corrugatedSeedRotation N)
      (corrugatedSeedInitialSpeed N ψ) (corrugatedSeedFrameHorizontal N ψ) r‖ ∧
    0 < inner ℝ (corrugatedSeedFrameHorizontal N ψ r)
      (corrugatedVisibilityDirection (1 / 4) (covariantSpeedCurve ell (corrugatedSeedRotation N)
        (corrugatedSeedInitialSpeed N ψ) (corrugatedSeedFrameHorizontal N ψ) r)) := by
  rw [corrugatedSeed_covariant_baseline (by linarith : 1 < N) hψ hcell]
  have hn : ‖-Complex.I‖ = 1 := by simp
  refine ⟨?_, ?_⟩
  · rw [norm_mul, hn, one_mul]
    exact (corrugatedSeedFrame_outer_visible hN hψ hi r).1
  · change 0 < inner ℝ (corrugatedAmbientHorizontal
      (normalLoopTangent (corrugatedSeedSphere N ∘ ψ) r)) _
    rw [corrugatedSeedFrame_horizontal (hψ.differentiable (by simp)),
      corrugatedVisibilityDirection_rotate (1 / 4) hn,
      real_inner_smul_left, corrugated_complex_inner_negI]
    exact mul_pos (sq_pos_of_pos (corrugatedSeedSphereScale_pos N _))
      (corrugatedSeedFrame_outer_visible hN hψ hi r).2.1

end
end TightVer401
