import TightVer401.SmoothingFlatModel
import TightVer401.SmoothingCutoffBounds

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff Matrix.Norms.Elementwise

def smoothingNormalHead (G R : Coord → ℝ) (θ : ℝ) (p : Coord) : Matrix (Fin 2) (Fin 2) ℝ :=
  planarHessian G p + seamSecondJet 0 0 (2 * θ * R p)

theorem smoothingNormalProfile_central_bounds (δ : ℝ) (hδ : 0 < δ) {t : ℝ}
    (ht : |t| ≤ δ) :
    |smoothingNormalProfile δ hδ t| ≤ 4 * δ^2 ∧
      |deriv (smoothingNormalProfile δ hδ) t| ≤ 4 * δ := by
  have htl := (abs_le.mp ht).1
  have htu := (abs_le.mp ht).2
  have hq := smoothingNormalProfile_bounds δ hδ htl
  have hd := smoothingNormalFirst_bounds δ hδ htl
  rw [(smoothingNormalProfile_hasDerivAt δ hδ t).deriv]
  constructor
  · rw [abs_of_nonneg hq.1]
    nlinarith [hq.2]
  · rw [abs_of_nonneg hd.1]
    linarith [hd.2]

/-- All error terms other than the convex normal Hessian entry vanish uniformly
with the smoothing radius, under actual first- and second-derivative bounds. -/
theorem smoothingNormalModel_head_bound {G R : Coord → ℝ}
    (hG : ContDiff ℝ ∞ G) (hR : ContDiff ℝ ∞ R) (δ : ℝ) (hδ : 0 < δ)
    {p : Coord} (ht : |p 1| ≤ δ) {M₁ M₂ : ℝ} (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hR₁ : ∀ i, |coordPartial i R p| ≤ M₁)
    (hR₂ : ∀ i j, |planarHessian R p i j| ≤ M₂) :
    ‖planarHessian (smoothingNormalModel (smoothingNormalProfile δ hδ) G R) p -
      smoothingNormalHead G R (smoothingNormalCDF δ hδ (p 1)) p‖ ≤
        8 * δ * M₁ + 4 * δ^2 * M₂ := by
  obtain ⟨hq, hd⟩ := smoothingNormalProfile_central_bounds δ hδ ht
  have hi (i : Fin 2) : |if i = 1 then deriv (smoothingNormalProfile δ hδ) (p 1) else 0| ≤ 4*δ := by
    split_ifs
    · exact hd
    · simp
      positivity
  have hb : 0 ≤ 8 * δ * M₁ + 4 * δ^2 * M₂ := by positivity
  apply (pi_norm_le_iff_of_nonneg hb).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg hb).mpr
  intro j
  rw [Real.norm_eq_abs]
  have he : (planarHessian (smoothingNormalModel (smoothingNormalProfile δ hδ) G R) p -
      smoothingNormalHead G R (smoothingNormalCDF δ hδ (p 1)) p) i j =
      (if j = 1 then deriv (smoothingNormalProfile δ hδ) (p 1) else 0) * coordPartial i R p +
      (if i = 1 then deriv (smoothingNormalProfile δ hδ) (p 1) else 0) * coordPartial j R p +
      smoothingNormalProfile δ hδ (p 1) * planarHessian R p i j := by
    change planarHessian (smoothingNormalModel (smoothingNormalProfile δ hδ) G R) p i j -
      (planarHessian G p i j + seamSecondJet 0 0 (2 * smoothingNormalCDF δ hδ (p 1) * R p) i j) = _
    rw [smoothingNormalModel_hessian (smoothingNormalProfile_contDiff δ hδ) hG hR,
      smoothingNormalProfile_second_deriv]
    fin_cases i <;> fin_cases j <;> simp [seamSecondJet] <;> ring
  rw [he]
  calc
    _ ≤ |(if j = 1 then deriv (smoothingNormalProfile δ hδ) (p 1) else 0) * coordPartial i R p| +
        |(if i = 1 then deriv (smoothingNormalProfile δ hδ) (p 1) else 0) * coordPartial j R p| +
        |smoothingNormalProfile δ hδ (p 1) * planarHessian R p i j| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (4*δ)*M₁ + (4*δ)*M₁ + (4*δ^2)*M₂ := by
      simp only [abs_mul]
      apply add_le_add
      · exact add_le_add (mul_le_mul (hi j) (hR₁ i) (abs_nonneg _) (by positivity))
          (mul_le_mul (hi i) (hR₁ j) (abs_nonneg _) (by positivity))
      · exact mul_le_mul hq (hR₂ i j) (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem smoothing_seamSecondJet_norm_bound (c : ℝ) : ‖seamSecondJet 0 0 c‖ ≤ |c| := by
  apply (pi_norm_le_iff_of_nonneg (abs_nonneg c)).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (abs_nonneg c)).mpr
  intro j
  fin_cases i <;> fin_cases j <;> simp [seamSecondJet]

end
end TightVer401
