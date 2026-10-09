import TightVer401.RadialCapConstants

namespace TightVer401
noncomputable section

def radialCapInverseRadius (R a ρ : ℝ) : ℝ := R - a * ρ / Real.sqrt (1 + ρ ^ 2)

theorem radialCap_inverse_disc {R a ρ : ℝ} (ha : 0 < a) :
    a ^ 2 - (R - radialCapInverseRadius R a ρ) ^ 2 =
      (a / Real.sqrt (1 + ρ ^ 2)) ^ 2 := by
  have hw : 0 < Real.sqrt (1 + ρ ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hsq := Real.sq_sqrt (show 0 ≤ 1 + ρ ^ 2 by positivity)
  dsimp [radialCapInverseRadius]
  field_simp
  nlinarith [hsq]

theorem radialCap_inverse_sqrt {R a ρ : ℝ} (ha : 0 < a) :
    Real.sqrt (a ^ 2 - (R - radialCapInverseRadius R a ρ) ^ 2) =
      a / Real.sqrt (1 + ρ ^ 2) := by
  have hw : 0 < Real.sqrt (1 + ρ ^ 2) := Real.sqrt_pos.mpr (by positivity)
  rw [radialCap_inverse_disc ha, Real.sqrt_sq (div_pos ha hw).le]

theorem radialCap_inverse_deriv {C R a ρ : ℝ} (ha : 0 < a) :
    deriv (radialCap C R a) (radialCapInverseRadius R a ρ) = ρ := by
  have hw : 0 < Real.sqrt (1 + ρ ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hdisc : 0 < a ^ 2 - (R - radialCapInverseRadius R a ρ) ^ 2 := by
    rw [radialCap_inverse_disc ha]
    exact sq_pos_of_pos (div_pos ha hw)
  rw [radialCap_deriv _ _ _ hdisc, radialCap_inverse_sqrt ha]
  dsimp [radialCapInverseRadius]
  field_simp
  <;> ring

theorem radialCap_inverse_legendre {C R a ρ : ℝ} (ha : 0 < a) :
    ρ * radialCapInverseRadius R a ρ - radialCap C R a (radialCapInverseRadius R a ρ) =
      R * ρ - a * Real.sqrt (1 + ρ ^ 2) - C := by
  have hw : 0 < Real.sqrt (1 + ρ ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hsq := Real.sq_sqrt (show 0 ≤ 1 + ρ ^ 2 by positivity)
  rw [radialCap, radialCap_inverse_sqrt ha]
  dsimp [radialCapInverseRadius]
  field_simp
  nlinarith [hsq]

theorem radialCap_inverse_radius_bounds {R a ρ : ℝ} (ha : 0 < a) (hρ : 0 < ρ) :
    R - a < radialCapInverseRadius R a ρ ∧ radialCapInverseRadius R a ρ < R := by
  have hw : 0 < Real.sqrt (1 + ρ ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hsq := Real.sq_sqrt (show 0 ≤ 1 + ρ ^ 2 by positivity)
  have hlt : ρ < Real.sqrt (1 + ρ ^ 2) := by nlinarith
  have hquot : a * ρ / Real.sqrt (1 + ρ ^ 2) < a := by
    apply (div_lt_iff₀ hw).mpr
    exact mul_lt_mul_of_pos_left hlt ha
  have hpos := div_pos (mul_pos ha hρ) hw
  dsimp [radialCapInverseRadius]
  constructor <;> linarith

end
end TightVer401
