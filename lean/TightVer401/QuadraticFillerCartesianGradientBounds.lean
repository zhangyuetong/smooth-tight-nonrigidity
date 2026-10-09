import TightVer401.QuadraticFillerCartesianConstruction
import TightVer401.DualRadialNeckGradientEscape

/-! Quantitative gradient escape for the retained quadratic part of the filler.
The large coefficient is chosen through the independent angular sign theorem. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

/-- Exact actual gradient radius of the retained quadratic germ, including the
outer endpoint of the inner half disk. -/
theorem quadraticFillerCartesian_radial_gradient_radius {R M d : ℝ}
    (_hR : 0 < R) (hM : 0 < M) {p : Coord}
    (hp : 0 < planarRadius p) (hpR : planarRadius p ≤ R / 2) :
    planarRadius (planarGradient (dualRadialQuadraticPotential R M d) p) =
      M * (R - planarRadius p) := by
  have hpR' : planarRadius p < R := by linarith
  have hdom : p ∈ radialPlanarDomain (Ioo 0 R) :=
    ⟨Real.sqrt_pos.mp hp, hp, hpR'⟩
  change planarRadius (planarGradient (radialPlanarPotential
    (dualRadialQuadraticProfile R M d)) p) = _
  rw [radialPlanarGradient_radius (dualRadialQuadraticProfile_contDiff R M d).contDiffOn
    isOpen_Ioo hdom, dualRadialQuadraticProfile_deriv,
    abs_of_pos (by nlinarith [mul_pos hM (sub_pos.mpr hpR')])]
  ring

/-- The whole retained inner half disk has gradient radius at least M R / 2. -/
theorem quadraticFillerCartesian_radial_gradient_radius_lower {R M d : ℝ}
    (hR : 0 < R) (hM : 0 < M) {p : Coord}
    (hp : 0 < planarRadius p) (hpR : planarRadius p ≤ R / 2) :
    M * R / 2 ≤ planarRadius (planarGradient (dualRadialQuadraticPotential R M d) p) := by
  rw [quadraticFillerCartesian_radial_gradient_radius hR hM hp hpR]
  nlinarith [mul_le_mul_of_nonneg_left hpR hM.le]

/-- On the strict inner disk, the actual Cartesian filler and retained radial
potential have equal germs, hence equal actual gradients. -/
theorem quadraticFillerCartesian_inner_gradient {R : ℝ} (hR : 0 < R) (M : ℝ)
    (h b : ℝ → ℝ) {p : Coord} (hp : planarRadius p < R / 2) :
    planarGradient (quadraticFillerCartesianPotential R M h b) p =
      planarGradient (dualRadialQuadraticPotential R M (-M * R^2 / 2)) p := by
  have hrad : Continuous planarRadius := by
    simpa only [angularDescentComplex_norm] using angularDescentComplex_contDiff.continuous.norm
  have heq : quadraticFillerCartesianPotential R M h b =ᶠ[𝓝 p]
      dualRadialQuadraticPotential R M (-M * R^2 / 2) := by
    filter_upwards [(isOpen_lt hrad continuous_const).mem_nhds hp] with q hq
    exact quadraticFillerCartesianPotential_inner_germ hR M h b hq.le
  ext i
  change fderiv ℝ (quadraticFillerCartesianPotential R M h b) p (Pi.single i 1) =
    fderiv ℝ (dualRadialQuadraticPotential R M (-M * R^2 / 2)) p (Pi.single i 1)
  rw [heq.fderiv_eq]

/-- Any requested inner gradient-radius lower bound can be imposed while the
actual Cartesian filler remains saddle on the entire closed punctured disk. -/
theorem exists_quadratic_cartesian_filler_large_gradient {R : ℝ} (hR : 0 < R)
    {h b : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (hb : ContDiff ℝ ∞ b)
    (hhper : Function.Periodic h (2 * Real.pi))
    (hbper : Function.Periodic b (2 * Real.pi))
    (hbpos : ∀ t, 0 < b t) (htrace : ∀ t, 0 < deriv (deriv h) t + R * b t)
    (M0 L : ℝ) :
    ∃ M : ℝ, M0 < M ∧ 0 < M ∧
      (∀ p : Coord, 0 < planarRadius p → planarRadius p ≤ R →
        (planarHessian (quadraticFillerCartesianPotential R M h b) p).det < 0 ∧
        gaussianCurvature (inducedMetric (planarSupportMap
          (quadraticFillerCartesianPotential R M h b))) p < 0) ∧
      (∀ p : Coord, 0 < planarRadius p → planarRadius p < R / 2 →
        L < planarRadius (planarGradient (quadraticFillerCartesianPotential R M h b) p)) := by
  obtain ⟨M, hbound, hM, _, _, _, hsign⟩ :=
    exists_quadratic_filler_coefficient_with_cutoff hR hh hb hhper hbper hbpos htrace
      (max M0 (2 * L / R))
  have hM0 : M0 < M := (le_max_left _ _).trans_lt hbound
  have hML : 2 * L / R < M := (le_max_right _ _).trans_lt hbound
  have hMR : 2 * L < M * R := (div_lt_iff₀ hR).mp hML
  refine ⟨M, hM0, hM, ?_, ?_⟩
  · intro p hp hpR
    exact quadraticFillerCartesianPotential_saddle hR hh hb hhper hbper hsign hp hpR
  · intro p hp hpR
    rw [quadraticFillerCartesian_inner_gradient hR M h b hpR]
    exact (show L < M * R / 2 by linarith).trans_le
      (quadraticFillerCartesian_radial_gradient_radius_lower hR hM hp hpR.le)

end
end TightVer401
