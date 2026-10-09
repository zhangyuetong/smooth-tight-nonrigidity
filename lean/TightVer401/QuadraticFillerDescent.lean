import TightVer401.AngularDescentCharts
import TightVer401.PolarSaddleSignOn

/-! Actual Cartesian descent of arbitrary smooth periodic cylinder data.
All derivatives are derivatives of the constructed scalar function. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

theorem angularDescent_punctured_isOpen : IsOpen {p : Coord | 0 < planarRadius p} := by
  exact isOpen_lt continuous_const (Real.continuous_sqrt.comp
    ((continuous_apply 0).pow 2 |>.add ((continuous_apply 1).pow 2)))

theorem angularDescentPotential_contDiffOn {W : Coord → ℝ} (hW : ContDiff ℝ ∞ W)
    (hperiod : ∀ r theta : ℝ, W ![r, theta + 2 * Real.pi] = W ![r, theta]) :
    ContDiffOn ℝ ∞ (angularDescentPotential W) {p | 0 < planarRadius p} := by
  intro p hp
  exact (angularDescentPotential_contDiffAt hW hperiod hp).contDiffWithinAt

/-- Exact blueprint interface: no angular filler, atlas transport, or descent
package is supplied as an input. The Cartesian potential is explicitly constructed. -/
theorem quadratic_filler_exists_cartesian_descent
    {W : Coord → ℝ} (hW : ContDiff ℝ ∞ W)
    (hperiod : ∀ r theta : ℝ,
      W ![r, theta + 2 * Real.pi] = W ![r, theta]) :
    ∃ F : Coord → ℝ, ContDiffOn ℝ ∞ F {p | 0 < planarRadius p} ∧
      ∀ q : Coord, 0 < q 0 → F (saddlePolarChart q) = W q := by
  exact ⟨angularDescentPotential W, angularDescentPotential_contDiffOn hW hperiod,
    fun _ hq => angularDescentPotential_polar hperiod hq⟩

/-- All positive-radius angle branches of one Cartesian point have equal data. -/
theorem angularDescent_well_defined {W : Coord → ℝ}
    (hperiod : ∀ r theta : ℝ, W ![r, theta + 2 * Real.pi] = W ![r, theta])
    {q q' : Coord} (hq : 0 < q 0) (hq' : 0 < q' 0)
    (he : saddlePolarChart q = saddlePolarChart q') : W q = W q' := by
  rw [← angularDescentPotential_polar hperiod hq,
    ← angularDescentPotential_polar hperiod hq', he]

/-- The pullback is an equality of germs on the open positive-radius cylinder. -/
theorem angularDescentPotential_polar_germ {W : Coord → ℝ}
    (hperiod : ∀ r theta : ℝ, W ![r, theta + 2 * Real.pi] = W ![r, theta])
    {q : Coord} (hq : 0 < q 0) :
    (fun x => angularDescentPotential W (saddlePolarChart x)) =ᶠ[𝓝 q] W := by
  filter_upwards [(isOpen_lt continuous_const (continuous_apply 0)).mem_nhds hq] with x hx
  exact angularDescentPotential_polar hperiod hx

theorem angularDescentPotential_polar_fderiv {W : Coord → ℝ}
    (hperiod : ∀ r theta : ℝ, W ![r, theta + 2 * Real.pi] = W ![r, theta])
    {q : Coord} (hq : 0 < q 0) :
    fderiv ℝ (fun x => angularDescentPotential W (saddlePolarChart x)) q = fderiv ℝ W q :=
  (angularDescentPotential_polar_germ hperiod hq).fderiv_eq

theorem angularDescentPotential_polar_coordPartial {W : Coord → ℝ}
    (hperiod : ∀ r theta : ℝ, W ![r, theta + 2 * Real.pi] = W ![r, theta])
    {q : Coord} (hq : 0 < q 0) (i : Fin 2) :
    coordPartial i (fun x => angularDescentPotential W (saddlePolarChart x)) q =
      coordPartial i W q := by
  unfold coordPartial
  rw [angularDescentPotential_polar_fderiv hperiod hq]

theorem angularDescentPotential_polar_planarHessian {W : Coord → ℝ}
    (hperiod : ∀ r theta : ℝ, W ![r, theta + 2 * Real.pi] = W ![r, theta])
    {q : Coord} (hq : 0 < q 0) :
    planarHessian (fun x => angularDescentPotential W (saddlePolarChart x)) q =
      planarHessian W q := by
  have he := angularDescentPotential_polar_germ hperiod hq
  have hd (j : Fin 2) : coordPartial j (fun x => angularDescentPotential W (saddlePolarChart x))
      =ᶠ[𝓝 q] coordPartial j W := by
    filter_upwards [he.eventuallyEq_nhds] with x hx
    unfold coordPartial
    rw [hx.fderiv_eq]
  ext i j
  unfold planarHessian coordPartial
  exact congrArg (fun d : Coord →L[ℝ] ℝ => d (Pi.single i 1)) ((hd j).fderiv_eq (𝕜 := ℝ))

/-- Actual Cartesian gradient chain rule, in the checked polar coordinate basis. -/
theorem angularDescentPotential_first_chain_rule {W : Coord → ℝ} (hW : ContDiff ℝ ∞ W)
    (hperiod : ∀ r theta : ℝ, W ![r, theta + 2 * Real.pi] = W ![r, theta])
    {q : Coord} (hq : 0 < q 0) (i : Fin 2) :
    coordPartial i W q = ∑ a : Fin 2,
      coordPartial a (angularDescentPotential W) (saddlePolarChart q) *
        coordPartial i (fun x => saddlePolarChart x a) q := by
  rw [← angularDescentPotential_polar_coordPartial hperiod hq]
  apply polarLocal_coordPartial_comp _ saddlePolarChart_contDiff
  exact (angularDescentPotential_contDiffAt hW hperiod
    (by simpa only [Set.mem_setOf_eq, angularDescent_radius_polar hq] using hq)).differentiableAt (by simp)

/-- Actual second derivatives include the second derivatives of the polar chart. -/
theorem angularDescentPotential_second_chain_rule {W : Coord → ℝ} (hW : ContDiff ℝ ∞ W)
    (hperiod : ∀ r theta : ℝ, W ![r, theta + 2 * Real.pi] = W ![r, theta])
    {q : Coord} (hq : 0 < q 0) (i j : Fin 2) :
    planarHessian W q i j =
      ((seamCoordinateJacobian saddlePolarChart q).transpose *
        planarHessian (angularDescentPotential W) (saddlePolarChart q) *
        seamCoordinateJacobian saddlePolarChart q) i j +
      ∑ a : Fin 2, coordPartial a (angularDescentPotential W) (saddlePolarChart q) *
        planarHessian (fun x => saddlePolarChart x a) q i j := by
  rw [← angularDescentPotential_polar_planarHessian hperiod hq]
  exact polarLocal_planarHessian_comp (angularDescentPotential_contDiffOn hW hperiod)
    angularDescent_punctured_isOpen saddlePolarChart_contDiff
    (by simpa only [Set.mem_setOf_eq, angularDescent_radius_polar hq] using hq) i j

/-- Cartesian Hessian determinant expressed entirely by the actual cylinder derivatives. -/
theorem angularDescentPotential_hessian_det {W : Coord → ℝ} (hW : ContDiff ℝ ∞ W)
    (hperiod : ∀ r theta : ℝ, W ![r, theta + 2 * Real.pi] = W ![r, theta])
    {q : Coord} (hq : 0 < q 0) :
    (planarHessian (angularDescentPotential W) (saddlePolarChart q)).det =
      (planarHessian W q 0 0 * (planarHessian W q 1 1 + q 0 * coordPartial 0 W q) -
        (planarHessian W q 0 1 - coordPartial 1 W q / q 0)^2) / q 0^2 := by
  rw [saddlePolarChart_hessian_det_on (angularDescentPotential_contDiffOn hW hperiod)
    angularDescent_punctured_isOpen (by simpa only [Set.mem_setOf_eq, angularDescent_radius_polar hq] using hq) hq.ne',
    angularDescentPotential_polar_planarHessian hperiod hq,
    angularDescentPotential_polar_coordPartial hperiod hq,
    angularDescentPotential_polar_coordPartial hperiod hq]

/-- Direct application bridge to the audited actual support curvature criterion. -/
theorem angularDescentPotential_gaussianCurvature_neg {W : Coord → ℝ} (hW : ContDiff ℝ ∞ W)
    (hperiod : ∀ r theta : ℝ, W ![r, theta + 2 * Real.pi] = W ![r, theta])
    {q : Coord} (hq : 0 < q 0) (hrr : planarHessian W q 0 0 < 0)
    (hang : 0 < planarHessian W q 1 1 + q 0 * coordPartial 0 W q) :
    gaussianCurvature (inducedMetric (planarSupportMap (angularDescentPotential W)))
      (saddlePolarChart q) < 0 := by
  apply saddlePolarChart_gaussianCurvature_neg_on
    (angularDescentPotential_contDiffOn hW hperiod) angularDescent_punctured_isOpen
    (by simpa only [Set.mem_setOf_eq, angularDescent_radius_polar hq] using hq) hq
  · rwa [angularDescentPotential_polar_planarHessian hperiod hq]
  · rwa [angularDescentPotential_polar_planarHessian hperiod hq,
      angularDescentPotential_polar_coordPartial hperiod hq]

end
end TightVer401

