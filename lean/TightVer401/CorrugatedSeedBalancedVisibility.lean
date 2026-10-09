import TightVer401.CorrugatedSeedFrameVisibility

namespace TightVer401
noncomputable section
open scoped ContDiff RealInnerProductSpace ComplexConjugate

def corrugatedSeedBalancedPartner (N : ℝ) (ψ : ℝ → ℝ) (ell : ℝ) (a : ℝ → ℝ) (r : ℝ) : ℂ :=
  Complex.I * covariantSpeedCurve ell (corrugatedSeedRotation N) a
    (corrugatedSeedFrameHorizontal N ψ) r

theorem corrugatedSeedBalancedPartner_contDiff (N ell : ℝ) {ψ a : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (corrugatedSeedBalancedPartner N ψ ell a) :=
  contDiff_const.mul (covariantSpeedCurve_contDiff ell _ ha
    (corrugatedSeedFrameHorizontal_contDiff N hψ))

theorem corrugatedSeedBalancedPartner_hasDerivAt (N ell : ℝ) {ψ a : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (ha : Continuous a) (r : ℝ) :
    HasDerivAt (corrugatedSeedBalancedPartner N ψ ell a)
      ((a r * (corrugatedSeedSphereScale N (ψ r))^2) •
        deriv (corrugatedSeedBeta N ∘ ψ) r) r := by
  have h := (covariantSpeedCurve_hasDerivAt ell (corrugatedSeedRotation N) ha
    (corrugatedSeedFrameHorizontal_contDiff N hψ).continuous r).const_mul Complex.I
  have he : Complex.I * (a r • corrugatedSeedFrameHorizontal N ψ r) =
      (a r * (corrugatedSeedSphereScale N (ψ r))^2) • deriv (corrugatedSeedBeta N ∘ ψ) r := by
    unfold corrugatedSeedFrameHorizontal
    rw [corrugatedSeedFrame_horizontal (hψ.differentiable (by simp))]
    simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_pow]
    calc
      _ = ((a r : ℂ) * ((corrugatedSeedSphereScale N (ψ r))^2 : ℂ)) *
          (-Complex.I * Complex.I) * deriv (corrugatedSeedBeta N ∘ ψ) r := by ring
      _ = _ := by simp
  exact he ▸ h

theorem corrugatedSeedBalancedPartner_reflected_visible {N : ℝ} (hN : 10000 ≤ N)
    {ψ a : ℝ → ℝ} {ell : ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hi : ∀ r, HasDerivAt ψ (corrugatedSeedSphericalSpeed N (ψ r))⁻¹ r)
    (ha : ContDiff ℝ ∞ a) (hapos : ∀ r, 0 < a r) :
    ComplexVisiblePair (4 / 5) (corrugatedReverseReflect (corrugatedSeedBalancedPartner N ψ ell a))
      (corrugatedReverseReflect (corrugatedSeedBeta N ∘ ψ)) := by
  intro r
  have hNr : 1 < N := by linarith
  have hpos : 0 < deriv ψ (-r) := by
    rw [(hi (-r)).deriv]
    exact inv_pos.mpr (corrugatedSeedSphericalSpeed_pos hNr _)
  have hbase : 0 < inner ℝ (deriv (corrugatedSeedBeta N ∘ ψ) (-r))
      (corrugatedReflectedVisibilityDirection (4 / 5) (corrugatedSeedBeta N (ψ (-r)))) := by
    rw [corrugatedComplex_comp_deriv ((corrugatedSeedBeta_contDiff N).differentiable (by simp))
      (hψ.differentiable (by simp)), real_inner_smul_left]
    exact mul_pos hpos (corrugatedSeed_inner_velocity_visibility hN _)
  have hp := corrugatedReverseReflect_hasDerivAt
    (corrugatedSeedBalancedPartner_hasDerivAt N ell hψ ha.continuous (-r))
  have hb := corrugatedReverseReflect_hasDerivAt
    (((corrugatedSeedBeta_contDiff N).comp hψ).differentiable (by simp) (-r)).hasDerivAt
  refine ⟨?_, ?_, ?_⟩
  · simp only [corrugatedReverseReflect, Function.comp_apply, Complex.norm_conj]
    linarith [corrugatedSeedBeta_radius_lower hN (ψ (-r))]
  · rw [hp.deriv]
    change 0 < inner ℝ (-conj ((a (-r) * (corrugatedSeedSphereScale N (ψ (-r)))^2) •
      deriv (corrugatedSeedBeta N ∘ ψ) (-r)))
      (corrugatedVisibilityDirection (4 / 5) (conj (corrugatedSeedBeta N (ψ (-r)))))
    rw [corrugated_reflection_inner, real_inner_smul_left]
    exact mul_pos (mul_pos (hapos (-r)) (sq_pos_of_pos (corrugatedSeedSphereScale_pos N _))) hbase
  · rw [hb.deriv]
    change 0 < inner ℝ (-conj (deriv (corrugatedSeedBeta N ∘ ψ) (-r)))
      (corrugatedVisibilityDirection (4 / 5) (conj (corrugatedSeedBeta N (ψ (-r)))))
    rw [corrugated_reflection_inner]
    exact hbase

end
end TightVer401
