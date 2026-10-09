import TightVer401.SmoothingFlatTaylor
import TightVer401.SmoothingNormalHessian
import TightVer401.SmoothingNormalProfileBounds

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry OAI.SmoothLocal.Geometry.HessianCalculus
open scoped ContDiff

/-- The actual normal interpolation; its Taylor remainder is constructed separately. -/
def smoothingNormalModel (f : ℝ → ℝ) (G R : Coord → ℝ) (p : Coord) : ℝ :=
  G p + f (p 1) * R p

theorem smoothingNormalModel_contDiff {f : ℝ → ℝ} {G R : Coord → ℝ}
    (hf : ContDiff ℝ ∞ f) (hG : ContDiff ℝ ∞ G) (hR : ContDiff ℝ ∞ R) :
    ContDiff ℝ ∞ (smoothingNormalModel f G R) :=
  hG.add ((smoothingNormalComposite_contDiff hf).mul hR)

theorem smoothingNormalModel_partial {f : ℝ → ℝ} {G R : Coord → ℝ}
    (hf : ContDiff ℝ ∞ f) (hG : ContDiff ℝ ∞ G) (hR : ContDiff ℝ ∞ R)
    (p : Coord) (i : Fin 2) :
    coordPartial i (smoothingNormalModel f G R) p = coordPartial i G p +
      (if i = 1 then deriv f (p 1) else 0) * R p + f (p 1) * coordPartial i R p := by
  change coordPartial i (fun q => G q + smoothingNormalComposite f q * R q) p = _
  rw [coordPartial_add_at (hG.differentiable (by simp) p)
    (((smoothingNormalComposite_contDiff hf).mul hR).differentiable (by simp) p),
    coordPartial_mul_at ((smoothingNormalComposite_contDiff hf).differentiable (by simp) p)
      (hR.differentiable (by simp) p), smoothingNormalComposite_partial hf]
  simp only [smoothingNormalComposite]
  ring

theorem smoothingNormalModel_hessian {f : ℝ → ℝ} {G R : Coord → ℝ}
    (hf : ContDiff ℝ ∞ f) (hG : ContDiff ℝ ∞ G) (hR : ContDiff ℝ ∞ R)
    (p : Coord) (i j : Fin 2) :
    planarHessian (smoothingNormalModel f G R) p i j = planarHessian G p i j +
      (seamSecondJet 0 0 (deriv (deriv f) (p 1))) i j * R p +
      (if j = 1 then deriv f (p 1) else 0) * coordPartial i R p +
      (if i = 1 then deriv f (p 1) else 0) * coordPartial j R p +
      f (p 1) * planarHessian R p i j := by
  change planarHessian (fun q => G q + smoothingNormalComposite f q * R q) p i j = _
  rw [smoothing_hessian_add hG ((smoothingNormalComposite_contDiff hf).mul hR),
    smoothing_hessian_mul (smoothingNormalComposite_contDiff hf) hR,
    smoothingNormalComposite_hessian hf,
    smoothingNormalComposite_partial hf, smoothingNormalComposite_partial hf]
  simp only [smoothingNormalComposite]
  ring

theorem smoothing_normal_square_deriv : deriv (fun t : ℝ => t^2) = fun t => 2*t := by
  funext t
  simpa using ((hasDerivAt_id t).pow 2).deriv

theorem smoothing_normal_square_second : deriv (deriv (fun t : ℝ => t^2)) = fun _ => 2 := by
  rw [smoothing_normal_square_deriv]
  funext t
  simpa using ((hasDerivAt_id t).const_mul 2).deriv

theorem smoothing_normal_quadratic_seam {R : Coord → ℝ} (hR : ContDiff ℝ ∞ R) (s : ℝ) :
    planarHessian (fun p : Coord => (p 1)^2 * R p) (![s,0]) =
      seamSecondJet 0 0 (2 * R (![s,0])) := by
  have hc (j : Fin 2) : coordPartial j (fun _ : Coord => (0 : ℝ)) = fun _ => 0 := by
    funext p
    simp [coordPartial]
  have hc₂ (p : Coord) (i j : Fin 2) : planarHessian (fun _ : Coord => (0 : ℝ)) p i j = 0 := by
    change coordPartial i (coordPartial j (fun _ : Coord => (0 : ℝ))) p = 0
    rw [hc]
    simp [coordPartial]
  have he : (fun p : Coord => (p 1)^2 * R p) =
      smoothingNormalModel (fun t : ℝ => t^2) (fun _ => 0) R := by
    funext p
    simp [smoothingNormalModel]
  rw [he]
  ext i j
  rw [smoothingNormalModel_hessian (by fun_prop) contDiff_const hR,
    smoothing_normal_square_second, smoothing_normal_square_deriv, hc₂]
  fin_cases i <;> fin_cases j <;> simp [seamSecondJet]

/-- The common flat first jet forces the actual Hessian difference to have just
one normal entry. No second-jet matching assumption is needed. -/
theorem smoothing_flat_difference_seam {D : Coord → ℝ} (hD : ContDiff ℝ ∞ D)
    (hzero : ∀ s : ℝ, D (![s,0]) = 0)
    (hfirst : ∀ s : ℝ, coordPartial 1 D (![s,0]) = 0) (s : ℝ) :
    planarHessian D (![s,0]) = seamSecondJet 0 0 (2 * smoothingFlatRemainder D (![s,0])) := by
  have he : D = fun p : Coord => (p 1)^2 * smoothingFlatRemainder D p := by
    funext p
    exact smoothing_flat_taylor_factor hD hzero hfirst p
  conv_lhs => rw [he]
  exact smoothing_normal_quadratic_seam (smoothingFlatRemainder_contDiff hD) s

theorem smoothingFlatRemainder_seam_second {D : Coord → ℝ} (hD : ContDiff ℝ ∞ D)
    (hzero : ∀ s : ℝ, D (![s,0]) = 0)
    (hfirst : ∀ s : ℝ, coordPartial 1 D (![s,0]) = 0) (s : ℝ) :
    2 * smoothingFlatRemainder D (![s,0]) = planarHessian D (![s,0]) 1 1 := by
  rw [smoothing_flat_difference_seam hD hzero hfirst]
  rfl

end
end TightVer401
