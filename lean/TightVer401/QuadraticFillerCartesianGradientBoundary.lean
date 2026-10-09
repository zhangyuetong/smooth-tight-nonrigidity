import TightVer401.QuadraticFillerCartesianConstruction
import TightVer401.QuadraticFillerCartesianJets
import TightVer401.PlanarGradientInverse

/-! Exact and quantitative consequences of the retained actual Cartesian boundary jet. -/
namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff Matrix

/-- The boundary gradient has the prescribed radial and tangential components. -/
theorem quadraticFillerCartesianGradient_boundary_components {R : ℝ} (hR : 0 < R)
    (M : ℝ) {h b : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (hb : ContDiff ℝ ∞ b)
    (hhper : Function.Periodic h (2 * Real.pi))
    (hbper : Function.Periodic b (2 * Real.pi)) (t : ℝ) :
    let g := planarGradient (quadraticFillerCartesianPotential R M h b)
      (saddlePolarChart ![R,t])
    g 0 * Real.cos t + g 1 * Real.sin t = b t ∧
      -g 0 * Real.sin t + g 1 * Real.cos t = deriv h t / R := by
  obtain ⟨_, hx, hy⟩ :=
    quadraticDominationCutoff_cartesian_boundary_first_jet hR M hh hb hhper hbper t
  change coordPartial 0 (quadraticFillerCartesianPotential R M h b) _ * Real.cos t +
    coordPartial 1 (quadraticFillerCartesianPotential R M h b) _ * Real.sin t = b t ∧ _
  change coordPartial 0 (quadraticFillerCartesianPotential R M h b) _ = _ at hx
  change coordPartial 1 (quadraticFillerCartesianPotential R M h b) _ = _ at hy
  change _ ∧ -coordPartial 0 (quadraticFillerCartesianPotential R M h b) _ * Real.sin t +
    coordPartial 1 (quadraticFillerCartesianPotential R M h b) _ * Real.cos t = deriv h t / R
  rw [hx, hy]
  constructor
  · linear_combination b t * Real.sin_sq_add_cos_sq t
  · linear_combination (deriv h t / R) * Real.sin_sq_add_cos_sq t

/-- The actual boundary gradient radius is determined exactly by the prescribed first jet. -/
theorem quadraticFillerCartesianGradient_boundary_radius_sq {R : ℝ} (hR : 0 < R)
    (M : ℝ) {h b : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (hb : ContDiff ℝ ∞ b)
    (hhper : Function.Periodic h (2 * Real.pi))
    (hbper : Function.Periodic b (2 * Real.pi)) (t : ℝ) :
    planarRadius (planarGradient (quadraticFillerCartesianPotential R M h b)
        (saddlePolarChart ![R,t])) ^ 2 = (b t)^2 + (deriv h t / R)^2 := by
  obtain ⟨_, hx, hy⟩ :=
    quadraticDominationCutoff_cartesian_boundary_first_jet hR M hh hb hhper hbper t
  rw [planarRadius_sq]
  change coordPartial 0 (quadraticFillerCartesianPotential R M h b) _ ^ 2 +
    coordPartial 1 (quadraticFillerCartesianPotential R M h b) _ ^ 2 = _
  change coordPartial 0 (quadraticFillerCartesianPotential R M h b) _ = _ at hx
  change coordPartial 1 (quadraticFillerCartesianPotential R M h b) _ = _ at hy
  rw [hx, hy]
  linear_combination ((b t)^2 + (deriv h t / R)^2) * Real.sin_sq_add_cos_sq t

/-- Positive periodic incoming radial slope supplies a uniform positive boundary-gradient margin. -/
theorem quadraticFillerCartesianGradient_boundary_margin {R : ℝ} (hR : 0 < R)
    {h b : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (hb : ContDiff ℝ ∞ b)
    (hhper : Function.Periodic h (2 * Real.pi))
    (hbper : Function.Periodic b (2 * Real.pi)) (hbpos : ∀ t, 0 < b t) :
    ∃ beta : ℝ, 0 < beta ∧ ∀ M t : ℝ,
      beta ≤ planarRadius (planarGradient (quadraticFillerCartesianPotential R M h b)
        (saddlePolarChart ![R,t])) := by
  let : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  obtain ⟨beta, hbeta, hbound⟩ := momentSlowdown_periodic_min (2 * Real.pi) hb hbper hbpos
  refine ⟨beta, hbeta, ?_⟩
  intro M t
  have heq := quadraticFillerCartesianGradient_boundary_radius_sq hR M hh hb hhper hbper t
  have hrad : 0 ≤ planarRadius (planarGradient (quadraticFillerCartesianPotential R M h b)
    (saddlePolarChart ![R,t])) := Real.sqrt_nonneg _
  have hb0 := hbpos t
  have hbeta' := hbound t
  nlinarith [sq_nonneg (deriv h t / R)]

end
end TightVer401
