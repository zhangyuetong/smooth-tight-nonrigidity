import TightVer401.RadialCapCalculus

namespace TightVer401
noncomputable section
open Set

def radialCapRadius (d s : ℝ) : ℝ := d * Real.sqrt (1 + s⁻¹ ^ 2)

theorem radialCapRadius_pos {d s : ℝ} (hd : 0 < d) (hs : 0 < s) :
    0 < radialCapRadius d s := by
  exact mul_pos hd (Real.sqrt_pos.mpr (by positivity))

theorem radialCapRadius_sq {d s : ℝ} :
    radialCapRadius d s ^ 2 = d ^ 2 * (1 + s⁻¹ ^ 2) := by
  rw [radialCapRadius, mul_pow, Real.sq_sqrt (by positivity)]

theorem radialCap_disc_positive {j d s r : ℝ} (hd : 0 < d) (hs : 0 < s)
    (hr : r ∈ Icc j (j + d)) : 0 < radialCapRadius d s ^ 2 - (j + d - r) ^ 2 := by
  have hpos : 0 < d ^ 2 * s⁻¹ ^ 2 := mul_pos (sq_pos_of_pos hd) (sq_pos_of_pos (inv_pos.mpr hs))
  rw [radialCapRadius_sq]
  have hleft : 0 ≤ j + d - r := by linarith [hr.2]
  have hright : j + d - r ≤ d := by linarith [hr.1]
  nlinarith

theorem radialCap_incoming_sqrt {d s : ℝ} (hd : 0 < d) (hs : 0 < s) :
    Real.sqrt (radialCapRadius d s ^ 2 - d ^ 2) = d / s := by
  have hsq : radialCapRadius d s ^ 2 - d ^ 2 = (d / s) ^ 2 := by
    rw [radialCapRadius_sq]
    simp only [div_eq_mul_inv, mul_pow]
    ring
  rw [hsq, Real.sqrt_sq (div_pos hd hs).le]

theorem radialCap_matches_first_jet {j d s value : ℝ} (hd : 0 < d) (hs : 0 < s) :
    radialCap (value - d / s) (j + d) (radialCapRadius d s) j = value ∧
      deriv (radialCap (value - d / s) (j + d) (radialCapRadius d s)) j = s := by
  have hdisc := radialCap_disc_positive hd hs (show j ∈ Icc j (j + d) by exact ⟨le_rfl, by linarith⟩)
  have hsub : j + d - j = d := by ring
  constructor
  · simp only [radialCap, hsub, radialCap_incoming_sqrt hd hs]
    ring
  · rw [radialCap_deriv _ _ _ hdisc, hsub, radialCap_incoming_sqrt hd hs]
    field_simp

theorem radialCap_strict_derivative_signs {j d s r C : ℝ} (hd : 0 < d) (hs : 0 < s)
    (hr : r ∈ Ico j (j + d)) :
    0 < deriv (radialCap C (j + d) (radialCapRadius d s)) r ∧
      deriv (deriv (radialCap C (j + d) (radialCapRadius d s))) r < 0 := by
  have hdisc := radialCap_disc_positive hd hs (show r ∈ Icc j (j + d) from ⟨hr.1, hr.2.le⟩)
  have hw := Real.sqrt_pos.mpr hdisc
  constructor
  · rw [radialCap_deriv _ _ _ hdisc]
    exact div_pos (sub_pos.mpr hr.2) hw
  · rw [radialCap_second_deriv _ _ _ hdisc]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (sq_pos_of_pos (radialCapRadius_pos hd hs)))
      (pow_pos hw 3)

theorem radialCap_endpoint_derivatives {C R a : ℝ} (ha : 0 < a) :
    deriv (radialCap C R a) R = 0 ∧ deriv (deriv (radialCap C R a)) R = -1 / a := by
  have hdisc : 0 < a ^ 2 - (R - R) ^ 2 := by simpa using sq_pos_of_pos ha
  constructor
  · rw [radialCap_deriv _ _ _ hdisc]
    simp
  · rw [radialCap_second_deriv _ _ _ hdisc]
    simp only [sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero, Real.sqrt_sq ha.le]
    field_simp

theorem exists_radialCap_small_width {j s : ℝ} (hj : 0 < j) (hs : 0 < s) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ d, 0 < d → d < ε → j + d > radialCapRadius d s := by
  let w := Real.sqrt (1 + s⁻¹ ^ 2)
  have hw : 0 < w := Real.sqrt_pos.mpr (by positivity)
  refine ⟨j / (w + 1), div_pos hj (by linarith), ?_⟩
  intro d hd hsmall
  have ht := (lt_div_iff₀ (by linarith : 0 < w + 1)).mp hsmall
  change d * w < j + d
  nlinarith

end
end TightVer401
