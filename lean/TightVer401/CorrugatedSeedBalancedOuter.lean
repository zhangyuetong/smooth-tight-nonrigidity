import TightVer401.CorrugatedSeedBalancedVisibility

namespace TightVer401
noncomputable section
open scoped ContDiff RealInnerProductSpace

theorem corrugated_complex_inner_I_right (z w : ℂ) :
    inner ℝ z (Complex.I * w) = inner ℝ (-Complex.I * z) w := by
  simp only [corrugated_complex_inner, Complex.mul_re, Complex.mul_im,
    Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
  ring

theorem corrugatedSeedBalancedPartner_outer_visible {N : ℝ} {ψ a : ℝ → ℝ} {ell : ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (ha : ContDiff ℝ ∞ a) (hapos : ∀ r, 0 < a r)
    (hvisible : ∀ r,
      (1 / 4 : ℝ) < ‖covariantSpeedCurve ell (corrugatedSeedRotation N) a
        (corrugatedSeedFrameHorizontal N ψ) r‖ ∧
      0 < inner ℝ (corrugatedSeedFrameHorizontal N ψ r)
        (corrugatedVisibilityDirection (1 / 4) (covariantSpeedCurve ell (corrugatedSeedRotation N) a
          (corrugatedSeedFrameHorizontal N ψ) r))) :
    ComplexVisiblePair (1 / 4) (corrugatedSeedBeta N ∘ ψ)
      (corrugatedSeedBalancedPartner N ψ ell a) := by
  intro r
  have hs : 0 < (corrugatedSeedSphereScale N (ψ r))^2 :=
    sq_pos_of_pos (corrugatedSeedSphereScale_pos N _)
  have hvis := (hvisible r).2
  change 0 < inner ℝ (corrugatedAmbientHorizontal
    (normalLoopTangent (corrugatedSeedSphere N ∘ ψ) r)) _ at hvis
  rw [corrugatedSeedFrame_horizontal (hψ.differentiable (by simp)), real_inner_smul_left] at hvis
  have hp := (mul_pos_iff_of_pos_left hs).mp hvis
  have hn : ‖Complex.I‖ = 1 := by simp
  have hb : 0 < inner ℝ (deriv (corrugatedSeedBeta N ∘ ψ) r)
      (corrugatedVisibilityDirection (1 / 4) (corrugatedSeedBalancedPartner N ψ ell a r)) := by
    unfold corrugatedSeedBalancedPartner
    rw [corrugatedVisibilityDirection_rotate (1 / 4) hn, corrugated_complex_inner_I_right]
    exact hp
  refine ⟨?_, hb, ?_⟩
  · simp only [corrugatedSeedBalancedPartner, norm_mul, hn, one_mul]
    exact (hvisible r).1
  · rw [(corrugatedSeedBalancedPartner_hasDerivAt N ell hψ ha.continuous r).deriv,
      real_inner_smul_left]
    exact mul_pos (mul_pos (hapos r) hs) hb

theorem corrugatedSeedBalancedPartner_initial {N : ℝ} (hN : 1 < N)
    {ψ : ℝ → ℝ} {ell : ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hcell : ∀ r, ψ (r + ell) = ψ r + corrugatedSeedCell N) :
    corrugatedSeedBalancedPartner N ψ ell (corrugatedSeedInitialSpeed N ψ) =
      corrugatedSeedPartner N ∘ ψ := by
  funext r
  unfold corrugatedSeedBalancedPartner
  rw [corrugatedSeed_covariant_baseline hN hψ hcell]
  simp [← mul_assoc]

end
end TightVer401
