import TightVer401.QuadraticFillerCartesianLegendreBoundaryDefinitions

/-! Ambient boundary jets belong to the actual smooth positive-radius radial continuation. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

/-- Literal radial continuation value at every positive polar radius. -/
theorem quadraticFillerCartesianLegendreRadial_polar_value {R M s : ℝ}
    (hM : 0 < M) (hs : 0 < s) (theta : ℝ) :
    quadraticFillerCartesianLegendreRadialPotential R M (saddlePolarChart ![s, theta]) =
      R * s - s ^ 2 / (2 * M) := by
  have hq : 0 < (![s, theta] : Coord) 0 := by simpa using hs
  have hradius : planarRadius (saddlePolarChart ![s, theta]) = s := by
    simpa using angularDescent_radius_polar hq
  change quadraticFillerCartesianLegendreRadialProfile R M
    (planarRadius (saddlePolarChart ![s, theta])) = _
  rw [hradius]
  exact quadraticFillerCartesianLegendreRadialProfile_eq hM s

/-- The actual ambient Cartesian gradient of the smooth radial continuation. -/
theorem quadraticFillerCartesianLegendreRadial_polar_gradient {R M s : ℝ}
    (hM : 0 < M) (hs : 0 < s) (theta : ℝ) :
    planarGradient (quadraticFillerCartesianLegendreRadialPotential R M)
        (saddlePolarChart ![s, theta]) =
      (R - s / M) • (![Real.cos theta, Real.sin theta] : Coord) := by
  have hq : 0 < (![s, theta] : Coord) 0 := by simpa using hs
  have hradius : planarRadius (saddlePolarChart ![s, theta]) = s := by
    simpa using angularDescent_radius_polar hq
  have hrpos : 0 < planarRadius (saddlePolarChart ![s, theta]) := by
    rw [hradius]; exact hs
  have hp : saddlePolarChart ![s, theta] ∈ radialPlanarDomain univ :=
    ⟨Real.sqrt_pos.mp hrpos, mem_univ _⟩
  have hpartial (i : Fin 2) :
      coordPartial i (quadraticFillerCartesianLegendreRadialPotential R M)
          (saddlePolarChart ![s, theta]) =
        (R - s / M) * saddlePolarChart ![s, theta] i / s := by
    change coordPartial i (radialPlanarPotential (quadraticFillerCartesianLegendreRadialProfile R M))
      (saddlePolarChart ![s, theta]) = _
    rw [radialPlanarPotential_coordPartial
      (quadraticFillerCartesianLegendreRadialProfile_contDiff R M).contDiffOn isOpen_univ hp,
      quadraticFillerCartesianLegendreRadialProfile_deriv hM, hradius]
  ext i
  change coordPartial i (quadraticFillerCartesianLegendreRadialPotential R M)
    (saddlePolarChart ![s, theta]) = _
  rw [hpartial]
  fin_cases i <;> simp [saddlePolarChart, Pi.smul_apply, smul_eq_mul]
  all_goals field_simp [hs.ne'] <;> ring

/-- Actual derivative in the outward radial unit direction. -/
theorem quadraticFillerCartesianLegendreRadial_polar_radial_derivative {R M s : ℝ}
    (hM : 0 < M) (hs : 0 < s) (theta : ℝ) :
    fderiv ℝ (quadraticFillerCartesianLegendreRadialPotential R M)
        (saddlePolarChart ![s, theta]) ![Real.cos theta, Real.sin theta] = R - s / M := by
  have hgradient := quadraticFillerCartesianLegendreRadial_polar_gradient (R := R) hM hs theta
  have hx : coordPartial 0 (quadraticFillerCartesianLegendreRadialPotential R M)
      (saddlePolarChart ![s, theta]) = (R - s / M) * Real.cos theta := by
    simpa [planarGradient] using congrFun hgradient 0
  have hy : coordPartial 1 (quadraticFillerCartesianLegendreRadialPotential R M)
      (saddlePolarChart ![s, theta]) = (R - s / M) * Real.sin theta := by
    simpa [planarGradient] using congrFun hgradient 1
  rw [seam_fderiv_coordinate_apply, hx, hy]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination (R - s / M) * Real.sin_sq_add_cos_sq theta

/-- Actual derivative in the angular tangent unit direction vanishes. -/
theorem quadraticFillerCartesianLegendreRadial_polar_tangent_derivative {R M s : ℝ}
    (hM : 0 < M) (hs : 0 < s) (theta : ℝ) :
    fderiv ℝ (quadraticFillerCartesianLegendreRadialPotential R M)
        (saddlePolarChart ![s, theta]) ![-Real.sin theta, Real.cos theta] = 0 := by
  have hgradient := quadraticFillerCartesianLegendreRadial_polar_gradient (R := R) hM hs theta
  have hx : coordPartial 0 (quadraticFillerCartesianLegendreRadialPotential R M)
      (saddlePolarChart ![s, theta]) = (R - s / M) * Real.cos theta := by
    simpa [planarGradient] using congrFun hgradient 0
  have hy : coordPartial 1 (quadraticFillerCartesianLegendreRadialPotential R M)
      (saddlePolarChart ![s, theta]) = (R - s / M) * Real.sin theta := by
    simpa [planarGradient] using congrFun hgradient 1
  rw [seam_fderiv_coordinate_apply, hx, hy]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- At the inner annulus boundary the outward annulus normal is the negative radial unit vector. -/
theorem quadraticFillerCartesianLegendreRadial_inner_boundary_first_jet {R M : ℝ}
    (hR : 0 < R) (hM : 0 < M) (theta : ℝ) :
    quadraticFillerCartesianLegendreRadialPotential R M
        (saddlePolarChart ![M * R / 2, theta]) = 3 * M * R ^ 2 / 8 ∧
      planarGradient (quadraticFillerCartesianLegendreRadialPotential R M)
          (saddlePolarChart ![M * R / 2, theta]) =
        (R / 2) • (![Real.cos theta, Real.sin theta] : Coord) ∧
      fderiv ℝ (quadraticFillerCartesianLegendreRadialPotential R M)
          (saddlePolarChart ![M * R / 2, theta]) ![Real.cos theta, Real.sin theta] = R / 2 ∧
      fderiv ℝ (quadraticFillerCartesianLegendreRadialPotential R M)
          (saddlePolarChart ![M * R / 2, theta]) (-![Real.cos theta, Real.sin theta]) = -R / 2 := by
  have hs : 0 < M * R / 2 := by positivity
  have hcoef : R - (M * R / 2) / M = R / 2 := by field_simp [hM.ne'] <;> ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [quadraticFillerCartesianLegendreRadial_polar_value hM hs theta]
    field_simp [hM.ne'] <;> ring
  · rw [quadraticFillerCartesianLegendreRadial_polar_gradient hM hs theta, hcoef]
  · rw [quadraticFillerCartesianLegendreRadial_polar_radial_derivative hM hs theta, hcoef]
  · rw [map_neg, quadraticFillerCartesianLegendreRadial_polar_radial_derivative hM hs theta,
      hcoef]
    ring

/-- At the outer annulus boundary the actual gradient and outward radial derivative vanish. -/
theorem quadraticFillerCartesianLegendreRadial_outer_boundary_first_jet {R M : ℝ}
    (hR : 0 < R) (hM : 0 < M) (theta : ℝ) :
    quadraticFillerCartesianLegendreRadialPotential R M
        (saddlePolarChart ![M * R, theta]) = M * R ^ 2 / 2 ∧
      planarGradient (quadraticFillerCartesianLegendreRadialPotential R M)
          (saddlePolarChart ![M * R, theta]) = 0 ∧
      fderiv ℝ (quadraticFillerCartesianLegendreRadialPotential R M)
          (saddlePolarChart ![M * R, theta]) ![Real.cos theta, Real.sin theta] = 0 := by
  have hs : 0 < M * R := mul_pos hM hR
  have hcoef : R - (M * R) / M = 0 := by field_simp [hM.ne'] <;> ring
  refine ⟨?_, ?_, ?_⟩
  · rw [quadraticFillerCartesianLegendreRadial_polar_value hM hs theta]
    field_simp [hM.ne'] <;> ring
  · rw [quadraticFillerCartesianLegendreRadial_polar_gradient hM hs theta, hcoef, zero_smul]
  · rw [quadraticFillerCartesianLegendreRadial_polar_radial_derivative hM hs theta, hcoef]

/-- Exact normal scalar expansion of the zero-constant radial dual profile. -/
theorem quadraticFillerCartesianLegendreRadial_normal_expansion {R M : ℝ}
    (hM : 0 < M) (s t : ℝ) :
    quadraticFillerCartesianLegendreRadialProfile R M (s + t) =
      quadraticFillerCartesianLegendreRadialProfile R M s + (R - s / M) * t - t ^ 2 / (2 * M) := by
  rw [quadraticFillerCartesianLegendreRadialProfile_eq hM,
    quadraticFillerCartesianLegendreRadialProfile_eq hM]
  field_simp [hM.ne'] <;> ring

/-- Exact polar normal expansion wherever both radii are positive. -/
theorem quadraticFillerCartesianLegendreRadial_polar_normal_expansion {R M s t : ℝ}
    (hM : 0 < M) (hs : 0 < s) (hst : 0 < s + t) (theta : ℝ) :
    quadraticFillerCartesianLegendreRadialPotential R M (saddlePolarChart ![s + t, theta]) =
      quadraticFillerCartesianLegendreRadialPotential R M (saddlePolarChart ![s, theta]) +
        (R - s / M) * t - t ^ 2 / (2 * M) := by
  rw [quadraticFillerCartesianLegendreRadial_polar_value hM hst theta,
    quadraticFillerCartesianLegendreRadial_polar_value hM hs theta]
  field_simp [hM.ne'] <;> ring

end
end TightVer401

