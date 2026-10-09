import TightVer401.QuadraticFillerCartesianConstruction

/-! The actual gradient of the filler on its exact inner radial germ and inner circles. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

/-- The exact germ transfers the retained radial derivative without angular assumptions. -/
theorem quadraticFillerCartesianPotential_inner_coordPartial {R : ℝ} (hR : 0 < R)
    (M : ℝ) (h b : ℝ → ℝ) {p : Coord} (hp : 0 < planarRadius p)
    (hpinner : planarRadius p < R / 2) (i : Fin 2) :
    coordPartial i (quadraticFillerCartesianPotential R M h b) p =
      M * (R - planarRadius p) * p i / planarRadius p := by
  have hrcont : Continuous planarRadius :=
    (((continuous_apply 0).pow 2).add ((continuous_apply 1).pow 2)).sqrt
  have he : quadraticFillerCartesianPotential R M h b =ᶠ[𝓝 p]
      dualRadialQuadraticPotential R M (-M * R ^ 2 / 2) :=
    by
      filter_upwards [(isOpen_lt hrcont continuous_const).mem_nhds hpinner] with q hq
      exact quadraticFillerCartesianPotential_inner_germ hR M h b hq.le
  have hpdom : p ∈ radialPlanarDomain univ :=
    ⟨Real.sqrt_pos.mp hp, mem_univ _⟩
  change fderiv ℝ (quadraticFillerCartesianPotential R M h b) p (Pi.single i 1) = _
  rw [he.fderiv_eq]
  change coordPartial i (radialPlanarPotential
    (dualRadialQuadraticProfile R M (-M * R ^ 2 / 2))) p = _
  rw [radialPlanarPotential_coordPartial
    (dualRadialQuadraticProfile_contDiff R M (-M * R ^ 2 / 2)).contDiffOn isOpen_univ hpdom,
    dualRadialQuadraticProfile_deriv]
  ring

/-- The actual Cartesian gradient traced on the source circle of radius rho. -/
def quadraticFillerCartesianGradientCircle (R M rho : ℝ) (h b : ℝ → ℝ)
    (theta : ℝ) : Coord :=
  ![coordPartial 0 (quadraticFillerCartesianPotential R M h b)
      (saddlePolarChart ![rho, theta]),
    coordPartial 1 (quadraticFillerCartesianPotential R M h b)
      (saddlePolarChart ![rho, theta])]

/-- The inner gradient is exactly the circle of radius M*(R-rho). -/
theorem quadraticFillerCartesianGradientCircle_eq {R rho : ℝ} (hR : 0 < R)
    (M : ℝ) (h b : ℝ → ℝ) (hrho : 0 < rho) (hrhoinner : rho < R / 2)
    (theta : ℝ) :
    quadraticFillerCartesianGradientCircle R M rho h b theta =
      ![M * (R - rho) * Real.cos theta, M * (R - rho) * Real.sin theta] := by
  have hq : 0 < (![rho, theta] : Coord) 0 := by simpa using hrho
  have hradius : planarRadius (saddlePolarChart ![rho, theta]) = rho := by
    simpa using angularDescent_radius_polar hq
  have hpartial (i : Fin 2) := quadraticFillerCartesianPotential_inner_coordPartial
    hR M h b (p := saddlePolarChart ![rho, theta])
    (by simpa [hradius] using hrho) (by simpa [hradius] using hrhoinner) i
  ext i
  fin_cases i
  · change coordPartial 0 (quadraticFillerCartesianPotential R M h b)
      (saddlePolarChart ![rho, theta]) = M * (R - rho) * Real.cos theta
    rw [hpartial 0, hradius]
    change M * (R - rho) * (rho * Real.cos theta) / rho =
      M * (R - rho) * Real.cos theta
    field_simp [hrho.ne']
  · change coordPartial 1 (quadraticFillerCartesianPotential R M h b)
      (saddlePolarChart ![rho, theta]) = M * (R - rho) * Real.sin theta
    rw [hpartial 1, hradius]
    change M * (R - rho) * (rho * Real.sin theta) / rho =
      M * (R - rho) * Real.sin theta
    field_simp [hrho.ne']

/-- The actual inner gradient circle is smooth, even for arbitrary angular traces. -/
theorem quadraticFillerCartesianGradientCircle_contDiff {R rho : ℝ} (hR : 0 < R)
    (M : ℝ) (h b : ℝ → ℝ) (hrho : 0 < rho) (hrhoinner : rho < R / 2) :
    ContDiff ℝ ∞ (quadraticFillerCartesianGradientCircle R M rho h b) := by
  have he := funext (quadraticFillerCartesianGradientCircle_eq hR M h b hrho hrhoinner)
  rw [he]
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · simpa using contDiff_const.mul Real.contDiff_cos
  · simpa using contDiff_const.mul Real.contDiff_sin

/-- The actual inner gradient circle closes with the source angular period. -/
theorem quadraticFillerCartesianGradientCircle_periodic {R rho : ℝ} (hR : 0 < R)
    (M : ℝ) (h b : ℝ → ℝ) (hrho : 0 < rho) (hrhoinner : rho < R / 2) :
    Function.Periodic (quadraticFillerCartesianGradientCircle R M rho h b) (2 * Real.pi) := by
  intro theta
  rw [quadraticFillerCartesianGradientCircle_eq hR M h b hrho hrhoinner,
    quadraticFillerCartesianGradientCircle_eq hR M h b hrho hrhoinner]
  simp

/-- Its angular tangent is the actual derivative of the constructed gradient curve. -/
theorem quadraticFillerCartesianGradientCircle_hasDerivAt {R rho : ℝ} (hR : 0 < R)
    (M : ℝ) (h b : ℝ → ℝ) (hrho : 0 < rho) (hrhoinner : rho < R / 2)
    (theta : ℝ) :
    HasDerivAt (quadraticFillerCartesianGradientCircle R M rho h b)
      ![-M * (R - rho) * Real.sin theta, M * (R - rho) * Real.cos theta] theta := by
  have he := funext (quadraticFillerCartesianGradientCircle_eq hR M h b hrho hrhoinner)
  rw [he]
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [mul_neg, neg_mul] using (Real.hasDerivAt_cos theta).const_mul (M * (R - rho))
  · simpa using (Real.hasDerivAt_sin theta).const_mul (M * (R - rho))

/-- The determinant of position and actual angular tangent is exactly the squared radius. -/
theorem quadraticFillerCartesianGradientCircle_orientation {R rho : ℝ} (hR : 0 < R)
    (M : ℝ) (h b : ℝ → ℝ) (hrho : 0 < rho) (hrhoinner : rho < R / 2)
    (theta : ℝ) :
    quadraticFillerCartesianGradientCircle R M rho h b theta 0 *
          deriv (quadraticFillerCartesianGradientCircle R M rho h b) theta 1 -
        quadraticFillerCartesianGradientCircle R M rho h b theta 1 *
          deriv (quadraticFillerCartesianGradientCircle R M rho h b) theta 0 =
      (M * (R - rho)) ^ 2 := by
  rw [(quadraticFillerCartesianGradientCircle_hasDerivAt hR M h b hrho hrhoinner theta).deriv,
    quadraticFillerCartesianGradientCircle_eq hR M h b hrho hrhoinner]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination (M * (R - rho)) ^ 2 * Real.sin_sq_add_cos_sq theta

/-- Positive coefficient yields a positive-radius, positively oriented regular circle. -/
theorem quadraticFillerCartesianGradientCircle_positive {R M rho : ℝ} (hR : 0 < R)
    (hM : 0 < M) (h b : ℝ → ℝ) (hrho : 0 < rho) (hrhoinner : rho < R / 2)
    (theta : ℝ) :
    0 < M * (R - rho) ∧
      planarRadius (quadraticFillerCartesianGradientCircle R M rho h b theta) =
        M * (R - rho) ∧
      0 < quadraticFillerCartesianGradientCircle R M rho h b theta 0 *
          deriv (quadraticFillerCartesianGradientCircle R M rho h b) theta 1 -
        quadraticFillerCartesianGradientCircle R M rho h b theta 1 *
          deriv (quadraticFillerCartesianGradientCircle R M rho h b) theta 0 ∧
      deriv (quadraticFillerCartesianGradientCircle R M rho h b) theta ≠ 0 := by
  have hrad : 0 < M * (R - rho) := mul_pos hM (by linarith)
  have horient : 0 < quadraticFillerCartesianGradientCircle R M rho h b theta 0 *
          deriv (quadraticFillerCartesianGradientCircle R M rho h b) theta 1 -
        quadraticFillerCartesianGradientCircle R M rho h b theta 1 *
          deriv (quadraticFillerCartesianGradientCircle R M rho h b) theta 0 := by
    rw [quadraticFillerCartesianGradientCircle_orientation hR M h b hrho hrhoinner]
    exact sq_pos_of_pos hrad
  refine ⟨hrad, ?_, horient, ?_⟩
  · rw [quadraticFillerCartesianGradientCircle_eq hR M h b hrho hrhoinner]
    change planarRadius (saddlePolarChart ![M * (R - rho), theta]) = M * (R - rho)
    exact angularDescent_radius_polar (by simpa using hrad)
  · intro hzero
    simp [hzero] at horient

end
end TightVer401
