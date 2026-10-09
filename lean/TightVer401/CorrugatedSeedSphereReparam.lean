import TightVer401.CorrugatedSeedSphereLift

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff RealInnerProductSpace

theorem sphericalCurve_comp_deriv {ζ : ℝ → Ambient} {ψ : ℝ → ℝ}
    (hζ : Differentiable ℝ ζ) (hψ : Differentiable ℝ ψ) (s : ℝ) :
    deriv (ζ ∘ ψ) s = deriv ψ s • deriv ζ (ψ s) :=
  ((hζ (ψ s)).hasDerivAt.scomp s (hψ s).hasDerivAt).deriv

theorem sphericalCurve_comp_second_deriv {ζ : ℝ → Ambient} {ψ : ℝ → ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (hψ : ContDiff ℝ ∞ ψ) (s : ℝ) :
    deriv (deriv (ζ ∘ ψ)) s = deriv (deriv ψ) s • deriv ζ (ψ s) +
      (deriv ψ s)^2 • deriv (deriv ζ) (ψ s) := by
  have hζd := hζ.differentiable (by simp)
  have hψd := hψ.differentiable (by simp)
  have hζd' := (contDiff_infty_iff_deriv.mp hζ).2.differentiable (by simp)
  have hψd' := (contDiff_infty_iff_deriv.mp hψ).2.differentiable (by simp)
  have he : deriv (ζ ∘ ψ) = fun r => deriv ψ r • deriv ζ (ψ r) :=
    funext (sphericalCurve_comp_deriv hζd hψd)
  rw [he]
  have hchain := (hζd' (ψ s)).hasDerivAt.scomp s (hψd s).hasDerivAt
  have hd := (hψd' s).hasDerivAt.smul hchain
  have hd' := hd.congr_of_eventuallyEq (f₁ := fun r => deriv ψ r • deriv ζ (ψ r))
    (Filter.Eventually.of_forall (fun _ => rfl))
  rw [hd'.deriv, smul_smul]
  rw [← sq]
  exact add_comm _ _

theorem normalLoopCurvature_comp {ζ : ℝ → Ambient} {ψ : ℝ → ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (hψ : ContDiff ℝ ∞ ψ) (s : ℝ) :
    normalLoopCurvature (ζ ∘ ψ) s = (deriv ψ s)^3 * normalLoopCurvature ζ (ψ s) := by
  unfold normalLoopCurvature normalLoopKappa normalLoopP
  rw [inner_neg_right, neg_neg, inner_neg_right, neg_neg,
    sphericalCurve_comp_deriv (hζ.differentiable (by simp)) (hψ.differentiable (by simp)),
    sphericalCurve_comp_second_deriv hζ hψ]
  simp only [Function.comp_apply]
  rw [normalLoopCross_smul_right, real_inner_smul_right, inner_add_left,
    real_inner_smul_left, real_inner_smul_left, ambientCross_orthogonal_right, mul_zero, zero_add]
  ring

end
end TightVer401
