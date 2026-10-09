import TightVer401.SmoothingFlatModel

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff

theorem smoothing_normal_quadratic_first_zero {R : Coord → ℝ}
    (hR : ContDiff ℝ ∞ R) (s : ℝ) (i : Fin 2) :
    coordPartial i (fun p : Coord => (p 1)^2*R p) (![s,0])=0 := by
  have he : (fun p : Coord => (p 1)^2*R p)=
      smoothingNormalModel (fun t : ℝ => t^2) (fun _ => 0) R := by
    funext p
    simp [smoothingNormalModel]
  have hc : coordPartial i (fun _ : Coord => (0 : ℝ)) (![s,0])=0 := by simp [coordPartial]
  rw [he,smoothingNormalModel_partial (by fun_prop) contDiff_const hR,
    smoothing_normal_square_deriv,hc]
  simp

theorem smoothing_flat_first_zero {D : Coord → ℝ} (hD : ContDiff ℝ ∞ D)
    (hzero : ∀ s : ℝ, D (![s,0])=0)
    (hfirst : ∀ s : ℝ, coordPartial 1 D (![s,0])=0) (s : ℝ) (i : Fin 2) :
    coordPartial i D (![s,0])=0 := by
  have he : D=fun p : Coord => (p 1)^2*smoothingFlatRemainder D p := by
    funext p
    exact smoothing_flat_taylor_factor hD hzero hfirst p
  conv_lhs => rw [he]
  exact smoothing_normal_quadratic_first_zero (smoothingFlatRemainder_contDiff hD) s i

end
end TightVer401
