import TightVer401.CorrugatedSeedVisibilityPositive
import TightVer401.CorrugatedSeedAnalytic

namespace TightVer401
noncomputable section
open scoped ComplexConjugate RealInnerProductSpace ContDiff

def ComplexVisiblePair (R : ℝ) (p δ : ℝ → ℂ) : Prop :=
  ∀ t, R < ‖δ t‖ ∧
    0 < inner ℝ (deriv p t) (corrugatedVisibilityDirection R (δ t)) ∧
    0 < inner ℝ (deriv δ t) (corrugatedVisibilityDirection R (δ t))

def corrugatedReverseReflect (f : ℝ → ℂ) (t : ℝ) : ℂ := conj (f (-t))

theorem corrugatedSeed_outer_velocity_visibility {N : ℝ} (hN : 10000 ≤ N) (t : ℝ) :
    0 < inner ℝ (deriv (corrugatedSeedBeta N) t)
      (corrugatedVisibilityDirection (1 / 4) (corrugatedSeedPartner N t)) := by
  have hNr : 1 < N := by linarith
  have h := corrugatedSeed_outer_normalized_visibility hN t
  unfold corrugatedSeedUnitTangent at h
  rw [real_inner_smul_left] at h
  have hn : 0 < ‖corrugatedSeedBetaVelocity N t‖ := norm_pos_iff.mpr
    (corrugatedSeedBetaVelocity_ne_zero hNr t)
  rw [corrugatedSeedBeta_deriv (ne_of_gt (by linarith : 0 < N))]
  exact (mul_pos_iff_of_pos_left (inv_pos.mpr hn)).mp h

theorem corrugatedSeed_inner_velocity_visibility {N : ℝ} (hN : 10000 ≤ N) (t : ℝ) :
    0 < inner ℝ (deriv (corrugatedSeedBeta N) t)
      (corrugatedReflectedVisibilityDirection (4 / 5) (corrugatedSeedBeta N t)) := by
  have hNr : 1 < N := by linarith
  have h := corrugatedSeed_inner_normalized_visibility hN t
  unfold corrugatedSeedUnitTangent at h
  rw [real_inner_smul_left] at h
  have hn : 0 < ‖corrugatedSeedBetaVelocity N t‖ := norm_pos_iff.mpr
    (corrugatedSeedBetaVelocity_ne_zero hNr t)
  rw [corrugatedSeedBeta_deriv (ne_of_gt (by linarith : 0 < N))]
  exact (mul_pos_iff_of_pos_left (inv_pos.mpr hn)).mp h

theorem corrugatedSeed_outer_visible {N : ℝ} (hN : 10000 ≤ N) :
    ComplexVisiblePair (1 / 4) (corrugatedSeedBeta N) (corrugatedSeedPartner N) := by
  intro t
  refine ⟨by linarith [(corrugatedSeedPartner_radius_bounds hN t).1],
    corrugatedSeed_outer_velocity_visibility hN t, ?_⟩
  rw [corrugatedSeedPartner_deriv (by linarith : 1 < N), real_inner_smul_left]
  exact mul_pos (corrugatedSeedMultiplier_pos _ _ _)
    (corrugatedSeed_outer_velocity_visibility hN t)

theorem corrugatedReverseReflect_hasDerivAt {f : ℝ → ℂ} {v : ℂ} {t : ℝ}
    (hf : HasDerivAt f v (-t)) :
    HasDerivAt (corrugatedReverseReflect f) (-conj v) t := by
  have h := (hf.scomp t (hasDerivAt_neg t)).star
  have h' := h.congr_of_eventuallyEq (f₁ := corrugatedReverseReflect f)
    (Filter.Eventually.of_forall (fun _ => rfl))
  have he : star ((-1 : ℝ) • v) = -conj v := by simp
  exact he ▸ h'

theorem corrugatedReverseReflect_contDiff {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (corrugatedReverseReflect f) := by
  change ContDiff ℝ ∞ (fun t => Complex.conjCLE (f (-t)))
  fun_prop

theorem corrugatedReverseReflect_periodic {f : ℝ → ℂ} {L : ℝ} (hf : Function.Periodic f L) :
    Function.Periodic (corrugatedReverseReflect f) L := by
  intro t
  unfold corrugatedReverseReflect
  have he : -(t + L) = -t - L := by ring
  rw [he, hf.sub_eq]

theorem corrugated_reflection_inner (R : ℝ) (v z : ℂ) :
    inner ℝ (-conj v) (corrugatedVisibilityDirection R (conj z)) =
      inner ℝ v (corrugatedReflectedVisibilityDirection R z) := by
  unfold corrugatedReflectedVisibilityDirection
  simp only [corrugated_complex_inner, Complex.neg_re, Complex.neg_im,
    Complex.conj_re, Complex.conj_im]
  ring

theorem corrugatedSeed_reflected_visible {N : ℝ} (hN : 10000 ≤ N) :
    ComplexVisiblePair (4 / 5) (corrugatedReverseReflect (corrugatedSeedPartner N))
      (corrugatedReverseReflect (corrugatedSeedBeta N)) := by
  intro t
  have hNr : 1 < N := by linarith
  have hNz : N ≠ 0 := ne_of_gt (by linarith)
  have hp := corrugatedReverseReflect_hasDerivAt
    (corrugatedSeedDelta_hasDerivAt (corrugatedSeedRoot N) N (-t))
  have hb := corrugatedReverseReflect_hasDerivAt (corrugatedSeedBeta_hasDerivAt hNz (-t))
  refine ⟨?_, ?_, ?_⟩
  · simp only [corrugatedReverseReflect, Complex.norm_conj]
    linarith [corrugatedSeedBeta_radius_lower hN (-t)]
  · change 0 < inner ℝ (deriv (corrugatedReverseReflect
      (corrugatedSeedDelta (corrugatedSeedRoot N) N)) t) _
    rw [hp.deriv]
    change 0 < inner ℝ (-conj (corrugatedSeedDeltaVelocity (corrugatedSeedRoot N) N (-t)))
      (corrugatedVisibilityDirection (4 / 5) (conj (corrugatedSeedBeta N (-t))))
    rw [corrugated_reflection_inner]
    have he : corrugatedSeedDeltaVelocity (corrugatedSeedRoot N) N (-t) =
        corrugatedSeedMultiplier (corrugatedSeedRoot N) N (-t) • deriv (corrugatedSeedBeta N) (-t) := by
      rw [corrugatedSeedBeta_deriv hNz]
      rfl
    rw [he, real_inner_smul_left]
    exact mul_pos (corrugatedSeedMultiplier_pos _ _ _)
      (corrugatedSeed_inner_velocity_visibility hN (-t))
  · rw [hb.deriv]
    change 0 < inner ℝ (-conj (corrugatedSeedBetaVelocity N (-t)))
      (corrugatedVisibilityDirection (4 / 5) (conj (corrugatedSeedBeta N (-t))))
    rw [corrugated_reflection_inner, ← corrugatedSeedBeta_deriv hNz]
    exact corrugatedSeed_inner_velocity_visibility hN (-t)

theorem corrugatedSeed_visible_closed_pairs {N : ℕ} (hN : 10000 ≤ N) :
    ContDiff ℝ ∞ (corrugatedSeedBeta (N : ℝ)) ∧
      ContDiff ℝ ∞ (corrugatedSeedPartner (N : ℝ)) ∧
      Function.Periodic (corrugatedSeedBeta (N : ℝ)) (2 * Real.pi) ∧
      Function.Periodic (corrugatedSeedPartner (N : ℝ)) (2 * Real.pi) ∧
      ComplexVisiblePair (1 / 4) (corrugatedSeedBeta (N : ℝ)) (corrugatedSeedPartner (N : ℝ)) ∧
      ComplexVisiblePair (4 / 5) (corrugatedReverseReflect (corrugatedSeedPartner (N : ℝ)))
        (corrugatedReverseReflect (corrugatedSeedBeta (N : ℝ))) := by
  have hNr : (10000 : ℝ) ≤ N := by exact_mod_cast hN
  exact ⟨corrugatedSeedBeta_contDiff _, corrugatedSeedPartner_contDiff _,
    corrugatedSeedBeta_periodic (by omega), corrugatedSeedPartner_periodic (by omega),
    corrugatedSeed_outer_visible hNr, corrugatedSeed_reflected_visible hNr⟩

end
end TightVer401
