import TightVer401.CorrugatedSeedVisibilityReference
import TightVer401.CorrugatedSeedUniformBounds

namespace TightVer401
noncomputable section
open scoped RealInnerProductSpace

theorem corrugatedSeedLimitingUnitTangent_norm (N t : ℝ) :
    ‖corrugatedSeedLimitingUnitTangent N t‖ = 1 := by
  have hn : 0 < ‖corrugatedSeedLimitingVelocity N t‖ := norm_pos_iff.mpr
    (mul_ne_zero (Complex.exp_ne_zero _) (corrugatedSeedLimitingFactor_ne_zero _))
  unfold corrugatedSeedLimitingUnitTangent
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ (ne_of_gt hn)]

theorem corrugated_inner_unit_perturbation (U V U₀ V₀ : ℂ) (hV : ‖V‖ = 1) (hU : ‖U₀‖ = 1) :
    |inner ℝ U V - inner ℝ U₀ V₀| ≤ ‖U - U₀‖ + ‖V - V₀‖ := by
  have he : inner ℝ U V - inner ℝ U₀ V₀ =
      inner ℝ (U - U₀) V + inner ℝ U₀ (V - V₀) := by
    rw [inner_sub_left, inner_sub_right]
    ring
  rw [he]
  have h1 := abs_real_inner_le_norm (U - U₀) V
  have h2 := abs_real_inner_le_norm U₀ (V - V₀)
  rw [hV, mul_one] at h1
  rw [hU, one_mul] at h2
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

theorem corrugatedSeedBeta_radius_lower {N : ℝ} (hN : 10000 ≤ N) (t : ℝ) :
    (99 / 100 : ℝ) ≤ ‖corrugatedSeedBeta N t‖ := by
  have hNp : 0 < N := by linarith
  rw [corrugatedSeedBeta_norm (by linarith)]
  have he : 1 / N ≤ (1 / 100 : ℝ) := (div_le_iff₀ hNp).mpr (by linarith)
  have h := (abs_le.mp ((corrugatedSeedRadius_error hNp t).trans he)).1
  linarith

theorem corrugatedSeed_outer_normalized_visibility {N : ℝ} (hN : 10000 ≤ N) (t : ℝ) :
    0 < inner ℝ (corrugatedSeedUnitTangent N t)
      (corrugatedVisibilityDirection (1 / 4) (corrugatedSeedPartner N t)) := by
  have hNp : 0 < N := by linarith
  have hNr : 1 < N := by linarith
  have hδ := corrugatedSeedPartner_radius_bounds hN t
  have hlim : ‖Complex.I / 2 * Complex.exp ((t : ℂ) * Complex.I)‖ = (1 / 2 : ℝ) := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    norm_num
  have hd := corrugatedVisibilityDirection_outer_distance hδ.1 hlim
  rw [corrugatedVisibilityDirection_outer_reference] at hd
  have hd' : ‖corrugatedVisibilityDirection (1 / 4) (corrugatedSeedPartner N t) -
      corrugatedOuterLimitingDirection t‖ ≤ 800 / N :=
    (hd.trans (mul_le_mul_of_nonneg_left (corrugatedSeedPartner_uniform_error hN t) (by norm_num))).trans_eq (by ring)
  have hv : ‖corrugatedVisibilityDirection (1 / 4) (corrugatedSeedPartner N t)‖ = 1 :=
    corrugatedVisibilityDirection_norm (by norm_num) (by linarith [hδ.1])
  have hi := corrugated_inner_unit_perturbation
    (corrugatedSeedUnitTangent N t) (corrugatedVisibilityDirection (1 / 4) (corrugatedSeedPartner N t))
    (corrugatedSeedLimitingUnitTangent N t) (corrugatedOuterLimitingDirection t)
    hv (corrugatedSeedLimitingUnitTangent_norm N t)
  have hb : |inner ℝ (corrugatedSeedUnitTangent N t)
        (corrugatedVisibilityDirection (1 / 4) (corrugatedSeedPartner N t)) -
      inner ℝ (corrugatedSeedLimitingUnitTangent N t) (corrugatedOuterLimitingDirection t)| ≤ 850 / N :=
    (hi.trans (add_le_add (corrugatedSeedUnitTangent_error hNr t).le hd')).trans_eq (by ring)
  have he : 850 / N ≤ (17 / 200 : ℝ) := (div_le_iff₀ hNp).mpr (by linarith)
  have hlo := (abs_le.mp (hb.trans he)).1
  have hm := corrugatedOuterLimitingDirection_margin N t
  linarith

theorem corrugatedSeed_inner_normalized_visibility {N : ℝ} (hN : 10000 ≤ N) (t : ℝ) :
    0 < inner ℝ (corrugatedSeedUnitTangent N t)
      (corrugatedReflectedVisibilityDirection (4 / 5) (corrugatedSeedBeta N t)) := by
  have hNp : 0 < N := by linarith
  have hNr : 1 < N := by linarith
  have hβ := corrugatedSeedBeta_radius_lower hN t
  have hd := corrugatedReflectedVisibilityDirection_inner_distance hβ (Complex.norm_exp_ofReal_mul_I t)
  rw [corrugatedReflectedVisibilityDirection_inner_reference] at hd
  have hd' : ‖corrugatedReflectedVisibilityDirection (4 / 5) (corrugatedSeedBeta N t) -
      corrugatedInnerLimitingDirection t‖ ≤ 15 / N :=
    (hd.trans (mul_le_mul_of_nonneg_left (corrugatedSeedBeta_error hNp t) (by norm_num))).trans_eq (by ring)
  have hv : ‖corrugatedReflectedVisibilityDirection (4 / 5) (corrugatedSeedBeta N t)‖ = 1 :=
    corrugatedReflectedVisibilityDirection_norm (by norm_num) (by linarith)
  have hi := corrugated_inner_unit_perturbation
    (corrugatedSeedUnitTangent N t) (corrugatedReflectedVisibilityDirection (4 / 5) (corrugatedSeedBeta N t))
    (corrugatedSeedLimitingUnitTangent N t) (corrugatedInnerLimitingDirection t)
    hv (corrugatedSeedLimitingUnitTangent_norm N t)
  have hb : |inner ℝ (corrugatedSeedUnitTangent N t)
        (corrugatedReflectedVisibilityDirection (4 / 5) (corrugatedSeedBeta N t)) -
      inner ℝ (corrugatedSeedLimitingUnitTangent N t) (corrugatedInnerLimitingDirection t)| ≤ 65 / N :=
    (hi.trans (add_le_add (corrugatedSeedUnitTangent_error hNr t).le hd')).trans_eq (by ring)
  have he : 65 / N ≤ (13 / 2000 : ℝ) := (div_le_iff₀ hNp).mpr (by linarith)
  have hlo := (abs_le.mp (hb.trans he)).1
  have hm := corrugatedInnerLimitingDirection_margin N t
  linarith

end
end TightVer401
