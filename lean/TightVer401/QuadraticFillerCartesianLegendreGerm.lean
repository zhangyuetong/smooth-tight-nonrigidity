import TightVer401.QuadraticFillerCartesianLegendreDefinitions

/-! The actual Legendre transform agrees on its open target with the retained radial dual. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The constructed actual Legendre transform has precisely the zero-constant radial dual. -/
theorem quadraticFillerCartesianLegendre_eq_radial {R M : ℝ} (hR : 0 < R)
    (hM : 0 < M) (h b : ℝ → ℝ) {y : Coord}
    (hy : y ∈ quadraticFillerCartesianGradientAnnulus R M) :
    quadraticFillerCartesianLegendrePotential hR hM h b y =
      quadraticFillerCartesianLegendreRadialPotential R M y := by
  have hypos : 0 < planarRadius y := (by positivity : 0 < M * R / 2).trans hy.1
  have hinverse := quadraticFillerCartesianGradient_inverse_mapsTo hR hM hy
  have hrinverse := quadraticFillerCartesianGradient_inverse_radius hR hM hy
  have hfiller := quadraticFillerCartesianPotential_inner_germ hR M h b hinverse.2.le
  have hdot : quadraticFillerCartesianGradientInverse R M y ⬝ᵥ y =
      (R - planarRadius y / M) * planarRadius y := by
    simp only [quadraticFillerCartesianGradientInverse, dotProduct, Fin.sum_univ_two,
      Pi.smul_apply, smul_eq_mul]
    calc
      _ = ((R - planarRadius y / M) / planarRadius y) * (y 0 ^ 2 + y 1 ^ 2) := by ring
      _ = (R - planarRadius y / M) * planarRadius y := by
        rw [← planarRadius_sq y]
        field_simp [hM.ne', hypos.ne'] <;> ring
  have hradial : quadraticFillerCartesianLegendreRadialPotential R M y =
      R * planarRadius y - planarRadius y ^ 2 / (2 * M) :=
    quadraticFillerCartesianLegendreRadialProfile_eq hM (planarRadius y)
  change quadraticFillerCartesianGradientInverse R M y ⬝ᵥ y -
    quadraticFillerCartesianPotential R M h b (quadraticFillerCartesianGradientInverse R M y) = _
  rw [hdot, hfiller, hradial]
  change (R - planarRadius y / M) * planarRadius y -
    dualRadialQuadraticProfile R M (-M * R ^ 2 / 2)
      (planarRadius (quadraticFillerCartesianGradientInverse R M y)) = _
  rw [hrinverse]
  unfold dualRadialQuadraticProfile
  field_simp [hM.ne'] <;> ring

/-- Equality holds as an actual germ at every point of the open target annulus. -/
theorem quadraticFillerCartesianLegendre_germ {R M : ℝ} (hR : 0 < R)
    (hM : 0 < M) (h b : ℝ → ℝ) {y : Coord}
    (hy : y ∈ quadraticFillerCartesianGradientAnnulus R M) :
    quadraticFillerCartesianLegendrePotential hR hM h b =ᶠ[𝓝 y]
      quadraticFillerCartesianLegendreRadialPotential R M := by
  filter_upwards [(quadraticFillerCartesianGradient_annulus_isOpen R M).mem_nhds hy] with z hz
  exact quadraticFillerCartesianLegendre_eq_radial hR hM h b hz

/-- The germ identifies the actual Cartesian Hessians, with no Hessian equality premise. -/
theorem quadraticFillerCartesianLegendre_hessian_eq_radial {R M : ℝ} (hR : 0 < R)
    (hM : 0 < M) (h b : ℝ → ℝ) {y : Coord}
    (hy : y ∈ quadraticFillerCartesianGradientAnnulus R M) :
    planarHessian (quadraticFillerCartesianLegendrePotential hR hM h b) y =
      planarHessian (quadraticFillerCartesianLegendreRadialPotential R M) y := by
  have he := quadraticFillerCartesianLegendre_germ hR hM h b hy
  ext i j
  have hj : coordPartial j (quadraticFillerCartesianLegendrePotential hR hM h b) =ᶠ[𝓝 y]
      coordPartial j (quadraticFillerCartesianLegendreRadialPotential R M) := by
    filter_upwards [he.fderiv (𝕜 := ℝ)] with z hz
    unfold coordPartial
    rw [hz]
  change fderiv ℝ (coordPartial j (quadraticFillerCartesianLegendrePotential hR hM h b)) y
      (Pi.single i 1) =
    fderiv ℝ (coordPartial j (quadraticFillerCartesianLegendreRadialPotential R M)) y
      (Pi.single i 1)
  rw [hj.fderiv_eq]

end
end TightVer401
