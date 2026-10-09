import TightVer401.QuadraticFillerCartesianGradientAnnulusDefinitions

/-! Exact forward and inverse algebra for the actual inner gradient annulus. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

/-- Radius scaling in the actual planar L2 radius, for a nonnegative scalar. -/
theorem quadraticFillerCartesianGradient_radius_smul {c : ℝ} (hc : 0 ≤ c) (p : Coord) :
    planarRadius (c • p) = c * planarRadius p := by
  have hsq : planarRadius (c • p) ^ 2 = (c * planarRadius p) ^ 2 := by
    simp only [planarRadius_sq, Pi.smul_apply, smul_eq_mul, mul_pow]
    ring
  exact (sq_eq_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hc (Real.sqrt_nonneg _))).mp hsq

/-- The actual Cartesian gradient agrees with the explicit radial map on the retained inner germ. -/
theorem quadraticFillerCartesianGradient_actual_eq {R : ℝ} (hR : 0 < R)
    (M : ℝ) (h b : ℝ → ℝ) {p : Coord} (hp : p ∈ quadraticFillerCartesianGradientInner R) :
    planarGradient (quadraticFillerCartesianPotential R M h b) p =
      quadraticFillerCartesianGradientRadialMap R M p := by
  ext i
  change coordPartial i (quadraticFillerCartesianPotential R M h b) p =
    (M * (R - planarRadius p) / planarRadius p) * p i
  rw [quadraticFillerCartesianPotential_inner_coordPartial hR M h b hp.1 hp.2]
  ring

/-- Exact forward radius on the positive strict inner disk. -/
theorem quadraticFillerCartesianGradient_radial_radius {R M : ℝ} (hR : 0 < R)
    (hM : 0 < M) {p : Coord} (hp : p ∈ quadraticFillerCartesianGradientInner R) :
    planarRadius (quadraticFillerCartesianGradientRadialMap R M p) =
      M * (R - planarRadius p) := by
  have hdiff : 0 < R - planarRadius p := by linarith [hp.2]
  rw [quadraticFillerCartesianGradientRadialMap,
    quadraticFillerCartesianGradient_radius_smul
      (div_nonneg (mul_nonneg hM.le hdiff.le) hp.1.le)]
  exact div_mul_cancel₀ (M * (R - planarRadius p)) hp.1.ne'

/-- Exact inverse radius on the explicit target annulus. -/
theorem quadraticFillerCartesianGradient_inverse_radius {R M : ℝ} (hR : 0 < R)
    (hM : 0 < M) {y : Coord} (hy : y ∈ quadraticFillerCartesianGradientAnnulus R M) :
    planarRadius (quadraticFillerCartesianGradientInverse R M y) =
      R - planarRadius y / M := by
  have hypos : 0 < planarRadius y := (by positivity : 0 < M * R / 2).trans hy.1
  have hyupper : planarRadius y / M < R :=
    (div_lt_iff₀ hM).mpr (by nlinarith [hy.2])
  have hdiff : 0 < R - planarRadius y / M := sub_pos.mpr hyupper
  rw [quadraticFillerCartesianGradientInverse,
    quadraticFillerCartesianGradient_radius_smul (div_nonneg hdiff.le hypos.le)]
  exact div_mul_cancel₀ (R - planarRadius y / M) hypos.ne'

/-- The explicit radial map takes the strict inner disk into the stated open annulus. -/
theorem quadraticFillerCartesianGradient_mapsTo {R M : ℝ} (hR : 0 < R) (hM : 0 < M) :
    MapsTo (quadraticFillerCartesianGradientRadialMap R M)
      (quadraticFillerCartesianGradientInner R) (quadraticFillerCartesianGradientAnnulus R M) := by
  intro p hp
  change M * R / 2 < planarRadius (quadraticFillerCartesianGradientRadialMap R M p) ∧
    planarRadius (quadraticFillerCartesianGradientRadialMap R M p) < M * R
  rw [quadraticFillerCartesianGradient_radial_radius hR hM hp]
  have hlow := mul_lt_mul_of_pos_left hp.2 hM
  have hhigh := mul_pos hM hp.1
  constructor <;> nlinarith

/-- The actual Cartesian gradient takes the same source into the same target annulus. -/
theorem quadraticFillerCartesianGradient_actual_mapsTo {R M : ℝ} (hR : 0 < R)
    (hM : 0 < M) (h b : ℝ → ℝ) :
    MapsTo (planarGradient (quadraticFillerCartesianPotential R M h b))
      (quadraticFillerCartesianGradientInner R) (quadraticFillerCartesianGradientAnnulus R M) := by
  intro p hp
  rw [quadraticFillerCartesianGradient_actual_eq hR M h b hp]
  exact quadraticFillerCartesianGradient_mapsTo hR hM hp

/-- The explicit inverse takes the open target annulus back into the strict inner disk. -/
theorem quadraticFillerCartesianGradient_inverse_mapsTo {R M : ℝ} (hR : 0 < R) (hM : 0 < M) :
    MapsTo (quadraticFillerCartesianGradientInverse R M)
      (quadraticFillerCartesianGradientAnnulus R M) (quadraticFillerCartesianGradientInner R) := by
  intro y hy
  change 0 < planarRadius (quadraticFillerCartesianGradientInverse R M y) ∧
    planarRadius (quadraticFillerCartesianGradientInverse R M y) < R / 2
  rw [quadraticFillerCartesianGradient_inverse_radius hR hM hy]
  have hyupper : planarRadius y / M < R :=
    (div_lt_iff₀ hM).mpr (by nlinarith [hy.2])
  have hylower : R / 2 < planarRadius y / M :=
    (lt_div_iff₀ hM).mpr (by nlinarith [hy.1])
  constructor <;> linarith

/-- The explicit inverse is a left inverse of the radial map on the source. -/
theorem quadraticFillerCartesianGradient_left_inverse {R M : ℝ} (hR : 0 < R)
    (hM : 0 < M) {p : Coord} (hp : p ∈ quadraticFillerCartesianGradientInner R) :
    quadraticFillerCartesianGradientInverse R M
      (quadraticFillerCartesianGradientRadialMap R M p) = p := by
  have hdiff : 0 < R - planarRadius p := by linarith [hp.2]
  change ((R - planarRadius (quadraticFillerCartesianGradientRadialMap R M p) / M) /
    planarRadius (quadraticFillerCartesianGradientRadialMap R M p)) •
      quadraticFillerCartesianGradientRadialMap R M p = p
  rw [quadraticFillerCartesianGradient_radial_radius hR hM hp,
    quadraticFillerCartesianGradientRadialMap, smul_smul]
  have hcoef : ((R - M * (R - planarRadius p) / M) / (M * (R - planarRadius p))) *
      (M * (R - planarRadius p) / planarRadius p) = 1 := by
    field_simp [hM.ne', hp.1.ne', hdiff.ne']
    ring
  rw [hcoef, one_smul]

/-- The radial map is a right inverse of the explicit inverse on the target. -/
theorem quadraticFillerCartesianGradient_right_inverse {R M : ℝ} (hR : 0 < R)
    (hM : 0 < M) {y : Coord} (hy : y ∈ quadraticFillerCartesianGradientAnnulus R M) :
    quadraticFillerCartesianGradientRadialMap R M
      (quadraticFillerCartesianGradientInverse R M y) = y := by
  have hypos : 0 < planarRadius y := (by positivity : 0 < M * R / 2).trans hy.1
  have hyupper : planarRadius y / M < R :=
    (div_lt_iff₀ hM).mpr (by nlinarith [hy.2])
  have hdiff : 0 < R - planarRadius y / M := sub_pos.mpr hyupper
  change (M * (R - planarRadius (quadraticFillerCartesianGradientInverse R M y)) /
    planarRadius (quadraticFillerCartesianGradientInverse R M y)) •
      quadraticFillerCartesianGradientInverse R M y = y
  rw [quadraticFillerCartesianGradient_inverse_radius hR hM hy,
    quadraticFillerCartesianGradientInverse, smul_smul]
  have hcoef : (M * (R - (R - planarRadius y / M)) / (R - planarRadius y / M)) *
      ((R - planarRadius y / M) / planarRadius y) = 1 := by
    have hden : M * R - planarRadius y ≠ 0 := (sub_pos.mpr hy.2).ne'
    field_simp [hM.ne', hypos.ne', hdiff.ne', hden]
    ring
  rw [hcoef, one_smul]

end
end TightVer401
