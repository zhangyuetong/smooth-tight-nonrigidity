import TightVer401.PlanarSupportForms
import OAI.Geometry.IsometricImmersion.Calculus.HessianCommutator

namespace TightVer401
noncomputable section
open Filter OAI.SmoothLocal.Geometry OAI.SmoothLocal.Geometry.HessianCalculus
open scoped ContDiff Topology

def smoothingCutoffBlend (χ F G : Coord → ℝ) (p : Coord) : ℝ :=
  G p + χ p * (F p - G p)

theorem smoothing_partial_contDiff {F : Coord → ℝ} (hF : ContDiff ℝ ∞ F) (i : Fin 2) :
    ContDiff ℝ ∞ (coordPartial i F) :=
  contDiffOn_univ.mp (partial_contDiffOn hF.contDiffOn isOpen_univ i)

theorem smoothing_hessian_add {F G : Coord → ℝ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (p : Coord) (i j : Fin 2) :
    planarHessian (fun q => F q + G q) p i j = planarHessian F p i j + planarHessian G p i j := by
  have hfirst : coordPartial j (fun q => F q + G q) =
      (fun q => coordPartial j F q + coordPartial j G q) := by
    funext q
    exact coordPartial_add_at (hF.differentiable (by simp) q) (hG.differentiable (by simp) q) j
  unfold planarHessian
  rw [hfirst]
  exact coordPartial_add_at ((smoothing_partial_contDiff hF j).differentiable (by simp) p)
    ((smoothing_partial_contDiff hG j).differentiable (by simp) p) i

theorem smoothing_hessian_sub {F G : Coord → ℝ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (p : Coord) (i j : Fin 2) :
    planarHessian (fun q => F q - G q) p i j = planarHessian F p i j - planarHessian G p i j := by
  have hfirst : coordPartial j (fun q => F q - G q) =
      (fun q => coordPartial j F q - coordPartial j G q) := by
    funext q
    exact coordPartial_sub_at (hF.differentiable (by simp) q) (hG.differentiable (by simp) q) j
  unfold planarHessian
  rw [hfirst]
  exact coordPartial_sub_at ((smoothing_partial_contDiff hF j).differentiable (by simp) p)
    ((smoothing_partial_contDiff hG j).differentiable (by simp) p) i

theorem smoothing_hessian_mul {F G : Coord → ℝ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (p : Coord) (i j : Fin 2) :
    planarHessian (fun q => F q * G q) p i j =
      planarHessian F p i j * G p + coordPartial j F p * coordPartial i G p +
      coordPartial i F p * coordPartial j G p + F p * planarHessian G p i j := by
  have hfirst : coordPartial j (fun q => F q * G q) =
      (fun q => coordPartial j F q * G q + F q * coordPartial j G q) := by
    funext q
    exact coordPartial_mul_at (hF.differentiable (by simp) q) (hG.differentiable (by simp) q) j
  have hpF := smoothing_partial_contDiff hF j
  have hpG := smoothing_partial_contDiff hG j
  unfold planarHessian
  rw [hfirst, coordPartial_add_at ((hpF.mul hG).differentiable (by simp) p)
    ((hF.mul hpG).differentiable (by simp) p),
    coordPartial_mul_at (hpF.differentiable (by simp) p) (hG.differentiable (by simp) p),
    coordPartial_mul_at (hF.differentiable (by simp) p) (hpG.differentiable (by simp) p)]
  ring

theorem smoothingCutoffBlend_contDiff {χ F G : Coord → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (smoothingCutoffBlend χ F G) := hG.add (hχ.mul (hF.sub hG))

theorem smoothingCutoffBlend_hessian {χ F G : Coord → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (p : Coord) (i j : Fin 2) :
    planarHessian (smoothingCutoffBlend χ F G) p i j =
      (1 - χ p) * planarHessian G p i j + χ p * planarHessian F p i j +
      coordPartial i χ p * (coordPartial j F p - coordPartial j G p) +
      coordPartial j χ p * (coordPartial i F p - coordPartial i G p) +
      (F p - G p) * planarHessian χ p i j := by
  unfold smoothingCutoffBlend
  rw [smoothing_hessian_add hG (hχ.mul (hF.sub hG)), smoothing_hessian_mul hχ (hF.sub hG),
    smoothing_hessian_sub hF hG,
    coordPartial_sub_at (hF.differentiable (by simp) p) (hG.differentiable (by simp) p) i,
    coordPartial_sub_at (hF.differentiable (by simp) p) (hG.differentiable (by simp) p) j]
  ring

theorem smoothingCutoffBlend_old_germ {χ F G : Coord → ℝ} {p : Coord}
    (hχ : χ =ᶠ[𝓝 p] (fun _ => 0)) : smoothingCutoffBlend χ F G =ᶠ[𝓝 p] G := by
  filter_upwards [hχ] with q hq
  simp [smoothingCutoffBlend, hq]

theorem smoothingCutoffBlend_new_germ {χ F G : Coord → ℝ} {p : Coord}
    (hχ : χ =ᶠ[𝓝 p] (fun _ => 1)) : smoothingCutoffBlend χ F G =ᶠ[𝓝 p] F := by
  filter_upwards [hχ] with q hq
  simp [smoothingCutoffBlend, hq]

end
end TightVer401
