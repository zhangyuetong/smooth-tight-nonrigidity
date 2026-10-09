import TightVer401.QuadraticFillerCartesianGradientAnnulusDefinitions

/-! Smoothness of the actual retained inner gradient and its explicit radial
inverse. No angular regularity or inverse identities are assumed. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

/-- The actual planar radius is continuous in the Cartesian coordinates. -/
theorem quadraticFillerCartesianGradient_radius_continuous : Continuous planarRadius :=
  (((continuous_apply 0).pow 2).add ((continuous_apply 1).pow 2)).sqrt

/-- The existing radial smoothness calculus on the positive-radius locus. -/
theorem quadraticFillerCartesianGradient_radius_contDiffOn :
    ContDiffOn ℝ ∞ planarRadius {p | 0 < planarRadius p} :=
  planarRadius_contDiffOn.mono (fun _ hp => Real.sqrt_pos.mp hp)

/-- The strict punctured inner disk is open. -/
theorem quadraticFillerCartesianGradient_inner_isOpen (R : ℝ) :
    IsOpen (quadraticFillerCartesianGradientInner R) :=
  (isOpen_lt continuous_const quadraticFillerCartesianGradient_radius_continuous).inter
    (isOpen_lt quadraticFillerCartesianGradient_radius_continuous continuous_const)

/-- The radial target annulus is open, independently of coefficient signs. -/
theorem quadraticFillerCartesianGradient_annulus_isOpen (R M : ℝ) :
    IsOpen (quadraticFillerCartesianGradientAnnulus R M) :=
  (isOpen_lt continuous_const quadraticFillerCartesianGradient_radius_continuous).inter
    (isOpen_lt quadraticFillerCartesianGradient_radius_continuous continuous_const)

/-- The exact radial germ supplies actual inner smoothness even for arbitrary
angular traces h and b. -/
theorem quadraticFillerCartesianGradient_potential_contDiffOn {R : ℝ} (hR : 0 < R)
    (M : ℝ) (h b : ℝ → ℝ) :
    ContDiffOn ℝ ∞ (quadraticFillerCartesianPotential R M h b)
      (quadraticFillerCartesianGradientInner R) := by
  have hradial : ContDiffOn ℝ ∞
      (dualRadialQuadraticPotential R M (-M * R^2 / 2))
      (quadraticFillerCartesianGradientInner R) :=
    (dualRadialQuadraticPotential_contDiffOn R M (-M * R^2 / 2)).mono (by
      intro p hp
      exact ⟨Real.sqrt_pos.mp hp.1, hp.1, by linarith [hp.2]⟩)
  exact hradial.congr (fun p hp => quadraticFillerCartesianPotential_inner_germ hR M h b hp.2.le)

/-- Smoothness of the actual inner Cartesian gradient follows from the generic
coordinate-gradient calculus on an open source. -/
theorem quadraticFillerCartesianGradient_contDiffOn {R : ℝ} (hR : 0 < R)
    (M : ℝ) (h b : ℝ → ℝ) :
    ContDiffOn ℝ ∞ (planarGradient (quadraticFillerCartesianPotential R M h b))
      (quadraticFillerCartesianGradientInner R) :=
  planarGradient_contDiffOn (quadraticFillerCartesianGradient_potential_contDiffOn hR M h b)
    (quadraticFillerCartesianGradient_inner_isOpen R)

/-- The explicit radial inverse expression is smooth everywhere off the origin.
Division by M is division by a constant; only the radial denominator needs
pointwise nonvanishing for this smoothness statement. -/
theorem quadraticFillerCartesianGradient_inverse_contDiffOn_positive (R M : ℝ) :
    ContDiffOn ℝ ∞ (quadraticFillerCartesianGradientInverse R M)
      {y | 0 < planarRadius y} := by
  unfold quadraticFillerCartesianGradientInverse
  have hrad := quadraticFillerCartesianGradient_radius_contDiffOn
  exact ((contDiffOn_const.sub (hrad.div_const M)).div hrad
    (fun _ hp => hp.ne')).smul contDiffOn_id

/-- For positive R and M the actual target annulus lies in the smooth inverse
locus; no inverse identity is a premise. -/
theorem quadraticFillerCartesianGradient_inverse_contDiffOn {R M : ℝ}
    (hR : 0 < R) (hM : 0 < M) :
    ContDiffOn ℝ ∞ (quadraticFillerCartesianGradientInverse R M)
      (quadraticFillerCartesianGradientAnnulus R M) :=
  (quadraticFillerCartesianGradient_inverse_contDiffOn_positive R M).mono (by
    intro y hy
    exact (show 0 < M * R / 2 by positivity).trans hy.1)

end
end TightVer401
