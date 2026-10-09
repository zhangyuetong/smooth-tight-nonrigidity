import TightVer401.QuadraticFillerCartesianLegendreBoundaryDefinitions

/-! A usable smooth collar for the actual retained radial dual continuation. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

/-- The actual radial dual is smooth at every positive radius, including both seams. -/
theorem quadraticFillerCartesianLegendreBoundary_contDiffOn_positive (R M : ℝ) :
    ContDiffOn ℝ ∞ (quadraticFillerCartesianLegendreRadialPotential R M)
      {y | 0 < planarRadius y} := by
  change ContDiffOn ℝ ∞ (radialPlanarPotential
    (quadraticFillerCartesianLegendreRadialProfile R M)) _
  exact (radialPlanarPotential_contDiffOn
    (quadraticFillerCartesianLegendreRadialProfile_contDiff R M).contDiffOn
      (U := univ)).mono (fun y hy => ⟨Real.sqrt_pos.mp hy, mem_univ _⟩)

/-- The concrete collar is open. -/
theorem quadraticFillerCartesianLegendreBoundary_collar_isOpen (R M : ℝ) :
    IsOpen (quadraticFillerCartesianLegendreBoundaryCollar R M) :=
  (isOpen_lt continuous_const quadraticFillerCartesianGradient_radius_continuous).inter
    (isOpen_lt quadraticFillerCartesianGradient_radius_continuous continuous_const)

/-- Both boundary circles and the closed annulus lie strictly inside this collar. -/
theorem quadraticFillerCartesianLegendreBoundary_closed_subset_collar {R M : ℝ}
    (hR : 0 < R) (hM : 0 < M) :
    quadraticFillerCartesianLegendreBoundaryClosedAnnulus R M ⊆
      quadraticFillerCartesianLegendreBoundaryCollar R M := by
  intro y hy
  have hMR := mul_pos hM hR
  exact ⟨by linarith [hy.1], by linarith [hy.2]⟩

/-- The collar stays away from the radial singularity. -/
theorem quadraticFillerCartesianLegendreBoundary_collar_subset_positive {R M : ℝ}
    (hR : 0 < R) (hM : 0 < M) :
    quadraticFillerCartesianLegendreBoundaryCollar R M ⊆ {y | 0 < planarRadius y} := by
  intro y hy
  exact (show 0 < M * R / 4 by positivity).trans hy.1

/-- Actual smoothness on a neighborhood of the closed target. -/
theorem quadraticFillerCartesianLegendreBoundary_collar_contDiffOn {R M : ℝ}
    (hR : 0 < R) (hM : 0 < M) :
    ContDiffOn ℝ ∞ (quadraticFillerCartesianLegendreRadialPotential R M)
      (quadraticFillerCartesianLegendreBoundaryCollar R M) :=
  (quadraticFillerCartesianLegendreBoundary_contDiffOn_positive R M).mono
    (quadraticFillerCartesianLegendreBoundary_collar_subset_positive hR hM)

/-- Actual ambient first-order differentiability holds at every retained boundary point. -/
theorem quadraticFillerCartesianLegendreBoundary_hasFDerivAt {R M : ℝ}
    (hR : 0 < R) (hM : 0 < M) {y : Coord}
    (hy : y ∈ quadraticFillerCartesianLegendreBoundaryClosedAnnulus R M) :
    HasFDerivAt (quadraticFillerCartesianLegendreRadialPotential R M)
      (fderiv ℝ (quadraticFillerCartesianLegendreRadialPotential R M) y) y := by
  exact ((quadraticFillerCartesianLegendreBoundary_collar_contDiffOn hR hM).contDiffAt
    ((quadraticFillerCartesianLegendreBoundary_collar_isOpen R M).mem_nhds
      (quadraticFillerCartesianLegendreBoundary_closed_subset_collar hR hM hy))).differentiableAt
      (by simp) |>.hasFDerivAt

/-- Ordinary smooth continuation contract: agreement with the actual local dual is
only asserted on its original open gradient image. -/
theorem quadraticFillerCartesianLegendreBoundary_smooth_extension {R M : ℝ}
    (hR : 0 < R) (hM : 0 < M) (h b : ℝ → ℝ) :
    IsOpen (quadraticFillerCartesianLegendreBoundaryCollar R M) ∧
      quadraticFillerCartesianLegendreBoundaryClosedAnnulus R M ⊆
        quadraticFillerCartesianLegendreBoundaryCollar R M ∧
      ContDiffOn ℝ ∞ (quadraticFillerCartesianLegendreRadialPotential R M)
        (quadraticFillerCartesianLegendreBoundaryCollar R M) ∧
      EqOn (quadraticFillerCartesianLegendrePotential hR hM h b)
        (quadraticFillerCartesianLegendreRadialPotential R M)
        (quadraticFillerCartesianGradientAnnulus R M) ∧
      ∀ y ∈ quadraticFillerCartesianGradientAnnulus R M,
        quadraticFillerCartesianLegendrePotential hR hM h b =ᶠ[𝓝 y]
          quadraticFillerCartesianLegendreRadialPotential R M :=
  ⟨quadraticFillerCartesianLegendreBoundary_collar_isOpen R M,
    quadraticFillerCartesianLegendreBoundary_closed_subset_collar hR hM,
    quadraticFillerCartesianLegendreBoundary_collar_contDiffOn hR hM,
    fun _ hy => quadraticFillerCartesianLegendre_eq_radial hR hM h b hy,
    fun _ hy => quadraticFillerCartesianLegendre_germ hR hM h b hy⟩

end
end TightVer401
