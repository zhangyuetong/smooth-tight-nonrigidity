import TightVer401.QuadraticFillerDescent
import TightVer401.QuadraticDominationPeriodicity
import TightVer401.QuadraticDominationGerms

/-! Cartesian first derivatives obtained by inverting the actual polar chain rule. -/
namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff Matrix BigOperators

/-- The actual Cartesian gradient of periodic cylinder data at a positive polar radius. -/
theorem angularDescentPotential_cartesian_gradient {W : Coord → ℝ}
    (hW : ContDiff ℝ ∞ W)
    (hperiod : ∀ r theta : ℝ, W ![r, theta + 2 * Real.pi] = W ![r, theta])
    {q : Coord} (hq : 0 < q 0) :
    coordPartial 0 (angularDescentPotential W) (saddlePolarChart q) =
        coordPartial 0 W q * Real.cos (q 1) -
          (coordPartial 1 W q / q 0) * Real.sin (q 1) ∧
      coordPartial 1 (angularDescentPotential W) (saddlePolarChart q) =
        coordPartial 0 W q * Real.sin (q 1) +
          (coordPartial 1 W q / q 0) * Real.cos (q 1) := by
  have hradial := angularDescentPotential_first_chain_rule hW hperiod hq 0
  have hangular := angularDescentPotential_first_chain_rule hW hperiod hq 1
  simp [Fin.sum_univ_two, saddlePolarChart_coordPartial] at hradial hangular
  have hangular_div : coordPartial 1 W q / q 0 =
      -coordPartial 0 (angularDescentPotential W) (saddlePolarChart q) * Real.sin (q 1) +
        coordPartial 1 (angularDescentPotential W) (saddlePolarChart q) * Real.cos (q 1) := by
    apply (div_eq_iff hq.ne').mpr
    rw [hangular]
    ring
  constructor
  · rw [hradial, hangular_div]
    linear_combination
      -coordPartial 0 (angularDescentPotential W) (saddlePolarChart q) *
        Real.sin_sq_add_cos_sq (q 1)
  · rw [hradial, hangular_div]
    linear_combination
      -coordPartial 1 (angularDescentPotential W) (saddlePolarChart q) *
        Real.sin_sq_add_cos_sq (q 1)

/-- The boundary value and actual Cartesian first jet for any admissible cutoff. -/
theorem dualQuadraticFiller_cartesian_boundary_first_jet {R : ℝ} (hR : 0 < R)
    (M : ℝ) {chi h b : ℝ → ℝ} (hchi : ContDiff ℝ ∞ chi)
    (hh : ContDiff ℝ ∞ h) (hb : ContDiff ℝ ∞ b)
    (hhper : Function.Periodic h (2 * Real.pi))
    (hbper : Function.Periodic b (2 * Real.pi))
    (hchi1 : ∀ r, 3 * R / 4 ≤ r → chi r = 1) (theta : ℝ) :
    angularDescentPotential (dualQuadraticFiller R M chi h b)
        (saddlePolarChart ![R, theta]) = h theta ∧
      coordPartial 0 (angularDescentPotential (dualQuadraticFiller R M chi h b))
          (saddlePolarChart ![R, theta]) =
        b theta * Real.cos theta - (deriv h theta / R) * Real.sin theta ∧
      coordPartial 1 (angularDescentPotential (dualQuadraticFiller R M chi h b))
          (saddlePolarChart ![R, theta]) =
        b theta * Real.sin theta + (deriv h theta / R) * Real.cos theta := by
  have hperiod : ∀ r theta : ℝ,
      dualQuadraticFiller R M chi h b ![r, theta + 2 * Real.pi] =
        dualQuadraticFiller R M chi h b ![r, theta] :=
    fun r theta => dualQuadraticFiller_angular_periodic R M (2 * Real.pi) hhper hbper r theta
  have hq : 0 < (![R, theta] : Coord) 0 := by simpa using hR
  obtain ⟨hvalue, hradial, hangular⟩ :=
    dualQuadraticFiller_boundary_first_jet hR M hchi hh hb hchi1 theta
  have hgradient := angularDescentPotential_cartesian_gradient
    (dualQuadraticFiller_contDiff R M hchi hh hb) hperiod hq
  refine ⟨?_, ?_, ?_⟩
  · exact (angularDescentPotential_polar hperiod hq).trans hvalue
  · simpa [hradial, hangular] using hgradient.1
  · simpa [hradial, hangular] using hgradient.2

/-- The constructed cutoff gives the explicit boundary Cartesian jet for every coefficient. -/
theorem quadraticDominationCutoff_cartesian_boundary_first_jet {R : ℝ} (hR : 0 < R)
    (M : ℝ) {h b : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (hb : ContDiff ℝ ∞ b)
    (hhper : Function.Periodic h (2 * Real.pi))
    (hbper : Function.Periodic b (2 * Real.pi)) (theta : ℝ) :
    angularDescentPotential (dualQuadraticFiller R M (quadraticDominationCutoff R) h b)
        (saddlePolarChart ![R, theta]) = h theta ∧
      coordPartial 0
          (angularDescentPotential (dualQuadraticFiller R M (quadraticDominationCutoff R) h b))
          (saddlePolarChart ![R, theta]) =
        b theta * Real.cos theta - (deriv h theta / R) * Real.sin theta ∧
      coordPartial 1
          (angularDescentPotential (dualQuadraticFiller R M (quadraticDominationCutoff R) h b))
          (saddlePolarChart ![R, theta]) =
        b theta * Real.sin theta + (deriv h theta / R) * Real.cos theta := by
  have hcutoff := quadraticDominationCutoff_properties hR
  exact dualQuadraticFiller_cartesian_boundary_first_jet hR M hcutoff.1 hh hb hhper hbper
    hcutoff.2.2.1 theta

end
end TightVer401
