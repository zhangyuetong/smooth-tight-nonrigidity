import TightVer401.RadialPlanarPotential

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

theorem radialPlanarPotential_hessian_det {F : ℝ → ℝ} {U : Set ℝ}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) {p : Coord}
    (hp : p ∈ radialPlanarDomain U) :
    (planarHessian (radialPlanarPotential F) p).det =
      deriv F (planarRadius p) * deriv (deriv F) (planarRadius p) / planarRadius p := by
  let A := deriv F (planarRadius p) / planarRadius p
  let B := deriv (deriv F) (planarRadius p) / planarRadius p^2 -
    deriv F (planarRadius p) / planarRadius p^3
  have hdet : (planarHessian (radialPlanarPotential F) p).det =
      A * (A + B * (p 0^2 + p 1^2)) := by
    rw [Matrix.det_fin_two]
    simp only [radialPlanarPotential_hessian hF hU hp]
    norm_num
    dsimp [A, B]
    ring
  have hr : planarRadius p ≠ 0 := (Real.sqrt_pos.mpr hp.1).ne'
  have hradial : A + B * (p 0^2 + p 1^2) = deriv (deriv F) (planarRadius p) := by
    rw [← planarRadius_sq p]
    dsimp [A, B]
    field_simp [hr] <;> ring
  rw [hdet, hradial]
  dsimp [A]
  ring

theorem radialPlanarPotential_hessian_det_neg {F : ℝ → ℝ} {U : Set ℝ}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) {p : Coord}
    (hp : p ∈ radialPlanarDomain U)
    (hprod : deriv F (planarRadius p) * deriv (deriv F) (planarRadius p) < 0) :
    (planarHessian (radialPlanarPotential F) p).det < 0 := by
  rw [radialPlanarPotential_hessian_det hF hU hp]
  exact div_neg_of_neg_of_pos hprod (Real.sqrt_pos.mpr hp.1)

theorem radialPlanarPotential_gaussianCurvature {F : ℝ → ℝ} {U : Set ℝ}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) {p : Coord}
    (hp : p ∈ radialPlanarDomain U)
    (hprod : deriv F (planarRadius p) * deriv (deriv F) (planarRadius p) ≠ 0) :
    gaussianCurvature (inducedMetric (planarSupportMap (radialPlanarPotential F))) p =
      planarRadius p / (planarWeight p^4 *
        (deriv F (planarRadius p) * deriv (deriv F) (planarRadius p))) := by
  have hr : planarRadius p ≠ 0 := (Real.sqrt_pos.mpr hp.1).ne'
  have hw : planarWeight p ≠ 0 := (planarWeight_pos p).ne'
  have hd : (planarHessian (radialPlanarPotential F) p).det ≠ 0 := by
    rw [radialPlanarPotential_hessian_det hF hU hp]
    exact div_ne_zero hprod hr
  rw [planarSupportMap_gaussianCurvature_at (radialPlanarPotential_contDiffOn hF)
    (radialPlanarDomain_isOpen hU) hp hd, radialPlanarPotential_hessian_det hF hU hp]
  field_simp [hr, hw, hprod] <;> ring

theorem radialPlanarPotential_gaussianCurvature_neg {F : ℝ → ℝ} {U : Set ℝ}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) {p : Coord}
    (hp : p ∈ radialPlanarDomain U)
    (hprod : deriv F (planarRadius p) * deriv (deriv F) (planarRadius p) < 0) :
    gaussianCurvature (inducedMetric (planarSupportMap (radialPlanarPotential F))) p < 0 := by
  have hd := radialPlanarPotential_hessian_det_neg hF hU hp hprod
  exact (planarSupportMap_negative_curvature_iff (radialPlanarPotential_contDiffOn hF)
    (radialPlanarDomain_isOpen hU) hp hd.ne).mpr hd

end
end TightVer401
