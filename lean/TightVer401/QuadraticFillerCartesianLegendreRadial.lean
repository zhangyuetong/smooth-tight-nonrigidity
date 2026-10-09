import TightVer401.QuadraticFillerCartesianGradientAnnulusDefinitions

/-! The zero-constant radial quadratic profile for the retained inner Legendre
transform. Geometry is adapted from the existing actual quadratic calculus;
equality with the Legendre transform is a separate composition theorem. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

/-- The corrected radial dual profile, represented by the retained quadratic API. -/
def quadraticFillerCartesianLegendreRadialProfile (R M : ℝ) : ℝ → ℝ :=
  dualRadialQuadraticProfile (M * R) (1 / M) 0

/-- Its actual Cartesian radial potential, with exactly zero additive constant. -/
def quadraticFillerCartesianLegendreRadialPotential (R M : ℝ) : Coord → ℝ :=
  dualRadialQuadraticPotential (M * R) (1 / M) 0

/-- Literal zero-constant profile identity for the positive filling coefficient. -/
theorem quadraticFillerCartesianLegendreRadialProfile_eq {R M : ℝ}
    (hM : 0 < M) (s : ℝ) :
    quadraticFillerCartesianLegendreRadialProfile R M s = R * s - s^2 / (2 * M) := by
  unfold quadraticFillerCartesianLegendreRadialProfile dualRadialQuadraticProfile
  field_simp [hM.ne']
  ring

/-- Smoothness is inherited directly from the retained quadratic profile. -/
theorem quadraticFillerCartesianLegendreRadialProfile_contDiff (R M : ℝ) :
    ContDiff ℝ ∞ (quadraticFillerCartesianLegendreRadialProfile R M) :=
  dualRadialQuadraticProfile_contDiff (M * R) (1 / M) 0

/-- Actual scalar derivative of the radial dual profile. -/
theorem quadraticFillerCartesianLegendreRadialProfile_hasDerivAt {R M : ℝ}
    (hM : 0 < M) (s : ℝ) :
    HasDerivAt (quadraticFillerCartesianLegendreRadialProfile R M) (R - s / M) s := by
  change HasDerivAt (dualRadialQuadraticProfile (M * R) (1 / M) 0) (R - s / M) s
  have hvalue : (1 / M) * (M * R) - (1 / M) * s = R - s / M := by
    field_simp [hM.ne']
  rw [← hvalue]
  exact dualRadialQuadraticProfile_hasDerivAt (M * R) (1 / M) 0 s

/-- The actual first derivative as a function on the entire scalar line. -/
theorem quadraticFillerCartesianLegendreRadialProfile_deriv {R M : ℝ} (hM : 0 < M) :
    deriv (quadraticFillerCartesianLegendreRadialProfile R M) = fun s => R - s / M := by
  funext s
  exact (quadraticFillerCartesianLegendreRadialProfile_hasDerivAt hM s).deriv

/-- The actual second derivative is the retained constant negative coefficient. -/
theorem quadraticFillerCartesianLegendreRadialProfile_second_deriv (R M : ℝ) :
    deriv (deriv (quadraticFillerCartesianLegendreRadialProfile R M)) = fun _ => -1 / M := by
  simpa [quadraticFillerCartesianLegendreRadialProfile, neg_div] using
    dualRadialQuadraticProfile_second_deriv (M * R) (1 / M) 0

/-- The radial profile has the required actual derivative signs on the target
annulus, without angular-data assumptions. -/
theorem quadraticFillerCartesianLegendreRadialProfile_signs {R M s : ℝ}
    (_hR : 0 < R) (hM : 0 < M) (hs : s ∈ Ioo (M * R / 2) (M * R)) :
    0 < deriv (quadraticFillerCartesianLegendreRadialProfile R M) s ∧
      deriv (deriv (quadraticFillerCartesianLegendreRadialProfile R M)) s < 0 :=
  dualRadialQuadraticProfile_signs (one_div_pos.mpr hM) hs.2

/-- The explicit gradient target lies in the retained radial quadratic domain. -/
theorem quadraticFillerCartesianLegendreRadial_annulus_subset {R M : ℝ}
    (hR : 0 < R) (hM : 0 < M) :
    quadraticFillerCartesianGradientAnnulus R M ⊆ radialPlanarDomain (Ioo 0 (M * R)) := by
  intro p hp
  have hpos : 0 < planarRadius p := (show 0 < M * R / 2 by positivity).trans hp.1
  exact ⟨Real.sqrt_pos.mp hpos, hpos, hp.2⟩

/-- Actual Cartesian smoothness of the radial dual potential on the target. -/
theorem quadraticFillerCartesianLegendreRadialPotential_contDiffOn {R M : ℝ}
    (hR : 0 < R) (hM : 0 < M) :
    ContDiffOn ℝ ∞ (quadraticFillerCartesianLegendreRadialPotential R M)
      (quadraticFillerCartesianGradientAnnulus R M) :=
  (dualRadialQuadraticPotential_contDiffOn (M * R) (1 / M) 0).mono
    (quadraticFillerCartesianLegendreRadial_annulus_subset hR hM)

/-- Actual Hessian determinant negativity, inherited from the quadratic geometry. -/
theorem quadraticFillerCartesianLegendreRadialPotential_hessian_det_neg {R M : ℝ}
    (hR : 0 < R) (hM : 0 < M) {p : Coord}
    (hp : p ∈ quadraticFillerCartesianGradientAnnulus R M) :
    (planarHessian (quadraticFillerCartesianLegendreRadialPotential R M) p).det < 0 :=
  dualRadialQuadraticPotential_hessian_det_neg (one_div_pos.mpr hM)
    (quadraticFillerCartesianLegendreRadial_annulus_subset hR hM hp)

/-- Actual intrinsic support curvature negativity on the retained target annulus. -/
theorem quadraticFillerCartesianLegendreRadialPotential_gaussianCurvature_neg {R M : ℝ}
    (hR : 0 < R) (hM : 0 < M) {p : Coord}
    (hp : p ∈ quadraticFillerCartesianGradientAnnulus R M) :
    gaussianCurvature (inducedMetric (planarSupportMap
      (quadraticFillerCartesianLegendreRadialPotential R M))) p < 0 :=
  dualRadialQuadraticPotential_gaussianCurvature_neg (one_div_pos.mpr hM)
    (quadraticFillerCartesianLegendreRadial_annulus_subset hR hM hp)

/-- Actual support-map differential injectivity on the retained target annulus. -/
theorem quadraticFillerCartesianLegendreRadialPotential_differential_injective {R M : ℝ}
    (hR : 0 < R) (hM : 0 < M) {p : Coord}
    (hp : p ∈ quadraticFillerCartesianGradientAnnulus R M) :
    Function.Injective (fderiv ℝ (planarSupportMap
      (quadraticFillerCartesianLegendreRadialPotential R M)) p) :=
  dualRadialQuadraticPotential_differential_injective (one_div_pos.mpr hM)
    (quadraticFillerCartesianLegendreRadial_annulus_subset hR hM hp)

end
end TightVer401
