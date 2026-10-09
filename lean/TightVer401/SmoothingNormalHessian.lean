import TightVer401.SmoothingCutoff
import TightVer401.SeamHessian
import TightVer401.SmoothingNormalProfile

namespace TightVer401
noncomputable section
open Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

def smoothingNormalComposite (f : ℝ → ℝ) (p : Coord) : ℝ := f (p 1)

theorem smoothingNormalComposite_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (smoothingNormalComposite f) := hf.comp (contDiff_apply ℝ ℝ 1)

theorem smoothingNormalComposite_hasFDerivAt {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (p : Coord) :
    HasFDerivAt (smoothingNormalComposite f)
      ((deriv f (p 1)) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1)) p := by
  have h := ((hf.differentiable (by simp) (p 1)).hasDerivAt.hasFDerivAt).comp p
    (hasFDerivAt_apply (𝕜 := ℝ) 1 p)
  have h' := h.congr_of_eventuallyEq (f₁ := smoothingNormalComposite f)
    (Eventually.of_forall (fun _ => rfl))
  have he : (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (deriv f (p 1))).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1) =
      (deriv f (p 1)) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1) := by
    ext v
    simp [mul_comm]
  exact he ▸ h'

theorem smoothingNormalComposite_partial {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (p : Coord) (i : Fin 2) :
    coordPartial i (smoothingNormalComposite f) p = if i = 1 then deriv f (p 1) else 0 := by
  unfold coordPartial
  rw [(smoothingNormalComposite_hasFDerivAt hf p).fderiv]
  fin_cases i <;> simp

theorem smoothingNormalComposite_hessian {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (p : Coord) :
    planarHessian (smoothingNormalComposite f) p = seamSecondJet 0 0 (deriv (deriv f) (p 1)) := by
  have h₀ : coordPartial 0 (smoothingNormalComposite f) = fun _ : Coord => 0 := by
    funext q
    simp only [smoothingNormalComposite_partial hf, if_neg (by decide : (0 : Fin 2) ≠ 1)]
  have h₁ : coordPartial 1 (smoothingNormalComposite f) = smoothingNormalComposite (deriv f) := by
    funext q
    simp [smoothingNormalComposite_partial hf, smoothingNormalComposite]
  ext i j
  fin_cases i <;> fin_cases j
  · change coordPartial 0 (coordPartial 0 (smoothingNormalComposite f)) p = 0
    rw [h₀]
    simp [coordPartial, seamSecondJet]
  · change coordPartial 0 (coordPartial 1 (smoothingNormalComposite f)) p = 0
    rw [h₁, smoothingNormalComposite_partial (contDiff_infty_iff_deriv.mp hf).2]
    simp
  · change coordPartial 1 (coordPartial 0 (smoothingNormalComposite f)) p = 0
    rw [h₀]
    simp [coordPartial]
  · change coordPartial 1 (coordPartial 1 (smoothingNormalComposite f)) p = deriv (deriv f) (p 1)
    rw [h₁, smoothingNormalComposite_partial (contDiff_infty_iff_deriv.mp hf).2]
    simp

theorem smoothingNormalProfile_planar_hessian (δ : ℝ) (hδ : 0 < δ) (p : Coord) :
    planarHessian (smoothingNormalComposite (smoothingNormalProfile δ hδ)) p =
      seamSecondJet 0 0 (2 * smoothingNormalCDF δ hδ (p 1)) := by
  rw [smoothingNormalComposite_hessian (smoothingNormalProfile_contDiff δ hδ),
    smoothingNormalProfile_second_deriv]

end
end TightVer401
