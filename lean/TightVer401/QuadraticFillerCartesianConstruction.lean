import TightVer401.QuadraticFillingDomination
import TightVer401.QuadraticFillerDescent

/-! Explicit Cartesian composition of the independently proved angular filler and descent. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

def quadraticFillerCartesianPotential (R M : ℝ) (h b : ℝ → ℝ) : Coord → ℝ :=
  angularDescentPotential (dualQuadraticFiller R M (quadraticDominationCutoff R) h b)

/-- Every actual Cartesian point has a principal polar representative, including the origin. -/
theorem quadraticFillerCartesian_polar_reconstruct (p : Coord) :
    saddlePolarChart ![planarRadius p, Complex.arg (angularDescentComplex p)] = p := by
  ext i
  fin_cases i
  · change planarRadius p * Real.cos (Complex.arg (angularDescentComplex p)) = p 0
    rw [← angularDescentComplex_norm p]
    simp [angularDescentComplex, Complex.norm_mul_cos_arg]
  · change planarRadius p * Real.sin (Complex.arg (angularDescentComplex p)) = p 1
    rw [← angularDescentComplex_norm p]
    simp [angularDescentComplex, Complex.norm_mul_sin_arg]

theorem quadraticFillerCartesianPotential_contDiffOn {R : ℝ} (hR : 0 < R) (M : ℝ)
    {h b : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (hb : ContDiff ℝ ∞ b)
    (hhper : Function.Periodic h (2 * Real.pi))
    (hbper : Function.Periodic b (2 * Real.pi)) :
    ContDiffOn ℝ ∞ (quadraticFillerCartesianPotential R M h b) {p | 0 < planarRadius p} := by
  apply angularDescentPotential_contDiffOn
    (dualQuadraticFiller_contDiff R M (quadraticDominationCutoff_properties hR).1 hh hb)
  intro r t
  exact dualQuadraticFiller_angular_periodic R M (2 * Real.pi) hhper hbper r t

theorem quadraticFillerCartesianPotential_polar (R M : ℝ) {h b : ℝ → ℝ}
    (hhper : Function.Periodic h (2 * Real.pi))
    (hbper : Function.Periodic b (2 * Real.pi)) {q : Coord} (hq : 0 < q 0) :
    quadraticFillerCartesianPotential R M h b (saddlePolarChart q) =
      dualQuadraticFiller R M (quadraticDominationCutoff R) h b q := by
  exact angularDescentPotential_polar
    (fun r t => dualQuadraticFiller_angular_periodic R M (2 * Real.pi) hhper hbper r t) hq

theorem quadraticFillerCartesianPotential_inner_germ {R : ℝ} (hR : 0 < R) (M : ℝ)
    (h b : ℝ → ℝ) {p : Coord} (hp : planarRadius p ≤ R / 2) :
    quadraticFillerCartesianPotential R M h b p =
      dualRadialQuadraticPotential R M (-M * R^2 / 2) p := by
  change dualQuadraticFiller R M (quadraticDominationCutoff R) h b
      ![planarRadius p, Complex.arg (angularDescentComplex p)] =
    dualRadialQuadraticProfile R M (-M * R^2 / 2) (planarRadius p)
  exact dualQuadraticFiller_inner_germ R M (quadraticDominationCutoff_properties hR).2.1
    (by simpa using hp)

/-- The angular strict signs imply actual Cartesian Hessian negativity at every positive point. -/
theorem quadraticFillerCartesianPotential_saddle {R M : ℝ} (hR : 0 < R)
    {h b : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (hb : ContDiff ℝ ∞ b)
    (hhper : Function.Periodic h (2 * Real.pi))
    (hbper : Function.Periodic b (2 * Real.pi))
    (hsign : ∀ q : Coord, 0 < q 0 → q 0 ≤ R →
      coordPartial 0 (coordPartial 0 (dualQuadraticFiller R M (quadraticDominationCutoff R) h b)) q < 0 ∧
      0 < coordPartial 1 (coordPartial 1 (dualQuadraticFiller R M (quadraticDominationCutoff R) h b)) q +
        q 0 * coordPartial 0 (dualQuadraticFiller R M (quadraticDominationCutoff R) h b) q)
    {p : Coord} (hp : 0 < planarRadius p) (hpR : planarRadius p ≤ R) :
    (planarHessian (quadraticFillerCartesianPotential R M h b) p).det < 0 ∧
      gaussianCurvature (inducedMetric (planarSupportMap (quadraticFillerCartesianPotential R M h b))) p < 0 := by
  let q : Coord := ![planarRadius p, Complex.arg (angularDescentComplex p)]
  have hq : 0 < q 0 := hp
  have hqR : q 0 ≤ R := hpR
  have hpolar : saddlePolarChart q = p := quadraticFillerCartesian_polar_reconstruct p
  have hW := dualQuadraticFiller_contDiff R M (quadraticDominationCutoff_properties hR).1 hh hb
  have hper : ∀ r t : ℝ,
      dualQuadraticFiller R M (quadraticDominationCutoff R) h b ![r,t + 2 * Real.pi] =
        dualQuadraticFiller R M (quadraticDominationCutoff R) h b ![r,t] :=
    fun r t => dualQuadraticFiller_angular_periodic R M (2 * Real.pi) hhper hbper r t
  obtain ⟨hrr, hang⟩ := hsign q hq hqR
  have hrr' : planarHessian (dualQuadraticFiller R M (quadraticDominationCutoff R) h b) q 0 0 < 0 := hrr
  have hang' : 0 < planarHessian (dualQuadraticFiller R M (quadraticDominationCutoff R) h b) q 1 1 +
      q 0 * coordPartial 0 (dualQuadraticFiller R M (quadraticDominationCutoff R) h b) q := hang
  have hdet : (planarHessian (quadraticFillerCartesianPotential R M h b) (saddlePolarChart q)).det < 0 := by
    change (planarHessian (angularDescentPotential _) (saddlePolarChart q)).det < 0
    rw [angularDescentPotential_hessian_det hW hper hq]
    apply div_neg_of_neg_of_pos _ (sq_pos_of_pos hq)
    have hmul := mul_neg_of_neg_of_pos hrr' hang'
    nlinarith [sq_nonneg (planarHessian (dualQuadraticFiller R M (quadraticDominationCutoff R) h b) q 0 1 -
      coordPartial 1 (dualQuadraticFiller R M (quadraticDominationCutoff R) h b) q / q 0)]
  have hK := angularDescentPotential_gaussianCurvature_neg hW hper hq hrr' hang'
  rw [hpolar] at hdet hK
  exact ⟨hdet, hK⟩

end
end TightVer401
