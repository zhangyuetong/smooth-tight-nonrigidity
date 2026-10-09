import TightVer401.QuadraticFillerCartesianConstruction
import TightVer401.QuadraticFillerCartesianJets
import TightVer401.QuadraticFillerCartesianCollar
import TightVer401.AngularDescentChartsNeighborhood

/-! An explicit smooth Cartesian filler with its actual first jet and open saddle locus. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix

/-- Arbitrarily large quadratic coefficients give an actual Cartesian saddle filler,
with retained boundary first jet, exact inner radial germ, and a derived open seam neighborhood. -/
theorem exists_quadratic_cartesian_filler {R : ℝ} (hR : 0 < R)
    {h b : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (hb : ContDiff ℝ ∞ b)
    (hhper : Function.Periodic h (2 * Real.pi))
    (hbper : Function.Periodic b (2 * Real.pi))
    (hbpos : ∀ t, 0 < b t) (htrace : ∀ t, 0 < deriv (deriv h) t + R * b t)
    (M0 : ℝ) :
    ∃ (M : ℝ) (F : Coord → ℝ) (U : Set Coord),
      M0 < M ∧ 0 < M ∧ F = quadraticFillerCartesianPotential R M h b ∧
      ContDiffOn ℝ ∞ F {p | 0 < planarRadius p} ∧
      (∀ q : Coord, 0 < q 0 → F (saddlePolarChart q) =
        dualQuadraticFiller R M (quadraticDominationCutoff R) h b q) ∧
      (∀ p : Coord, 0 < planarRadius p → planarRadius p ≤ R →
        (planarHessian F p).det < 0 ∧
          gaussianCurvature (inducedMetric (planarSupportMap F)) p < 0) ∧
      (∀ theta : ℝ, F (saddlePolarChart ![R, theta]) = h theta ∧
        coordPartial 0 F (saddlePolarChart ![R, theta]) =
          b theta * Real.cos theta - (deriv h theta / R) * Real.sin theta ∧
        coordPartial 1 F (saddlePolarChart ![R, theta]) =
          b theta * Real.sin theta + (deriv h theta / R) * Real.cos theta) ∧
      (∀ p : Coord, 0 < planarRadius p → planarRadius p ≤ R / 2 →
        F p = dualRadialQuadraticPotential R M (-M * R^2 / 2) p) ∧
      IsOpen U ∧ U ⊆ {p | 0 < planarRadius p} ∧ ContDiffOn ℝ ∞ F U ∧
      (∀ p : Coord, 0 < planarRadius p → planarRadius p ≤ R → p ∈ U) ∧
      (∀ p ∈ U, (planarHessian F p).det < 0 ∧
        gaussianCurvature (inducedMetric (planarSupportMap F)) p < 0) := by
  obtain ⟨hchi, hc0, hc1, _⟩ := quadraticDominationCutoff_properties hR
  obtain ⟨M, hM0, hM, hsign⟩ :=
    exists_quadratic_filler_coefficient hR hchi hh hb hhper hbper hc0 hc1 hbpos htrace M0
  let F := quadraticFillerCartesianPotential R M h b
  have hF : ContDiffOn ℝ ∞ F {p | 0 < planarRadius p} :=
    quadraticFillerCartesianPotential_contDiffOn hR M hh hb hhper hbper
  have hsaddle : ∀ p : Coord, 0 < planarRadius p → planarRadius p ≤ R →
      (planarHessian F p).det < 0 ∧
        gaussianCurvature (inducedMetric (planarSupportMap F)) p < 0 :=
    fun p hp hpR => quadraticFillerCartesianPotential_saddle hR hh hb hhper hbper hsign hp hpR
  obtain ⟨U, hU, hsub, hcontains, hFU, hdetU, hKU⟩ :=
    quadraticFillerCartesian_exists_open_saddle_neighborhood hF
      (fun p hp hpR => (hsaddle p hp hpR).1)
  refine ⟨M, F, U, hM0, hM, rfl, hF, ?_, hsaddle, ?_, ?_, hU, hsub, hFU,
    hcontains, fun p hp => ⟨hdetU p hp, hKU p hp⟩⟩
  · exact fun q hq => quadraticFillerCartesianPotential_polar R M hhper hbper hq
  · exact quadraticDominationCutoff_cartesian_boundary_first_jet hR M hh hb hhper hbper
  · exact fun p _ hpR => quadraticFillerCartesianPotential_inner_germ hR M h b hpR

end
end TightVer401
