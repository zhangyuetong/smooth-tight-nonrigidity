import TightVer401.SeamNormalCoordinates
import TightVer401.SeamFrameJet

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix

/-- Actual gradient agreement along the curve implies equality of both the
tangential and mixed Cartesian Hessian entries in the tangent-normal frame. -/
theorem relativeSaddleSeam_shared_entries {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ ∞ γ) {f g : Coord → ℝ} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) (hU : IsOpen U)
    (hSeam : ∀ s, seamComplexCoord (γ s) ∈ U)
    (hGradient : ∀ s, planarGradient f (seamComplexCoord (γ s)) =
      planarGradient g (seamComplexCoord (γ s))) (s : ℝ) :
    ∀ i : Fin 2,
      seamFramedHessian f (seamComplexCoord (γ s))
        (seamComplexCoord (deriv γ s)) (seamComplexCoord (Complex.I * deriv γ s)) i 0 =
      seamFramedHessian g (seamComplexCoord (γ s))
        (seamComplexCoord (deriv γ s)) (seamComplexCoord (Complex.I * deriv γ s)) i 0 := by
  have hd : HasDerivAt (fun t => seamComplexCoord (γ t))
      (seamComplexCoord (deriv γ s)) s :=
    seamComplexCoord.hasFDerivAt.comp_hasDerivAt s
      ((hγ.differentiable (by simp) s).hasDerivAt)
  have ha := seam_hessian_tangent_action hf hg hU hd.differentiableAt (hSeam s)
    (Eventually.of_forall hGradient)
  rw [hd.deriv] at ha
  exact seamFramedHessian_first_column ha

/-- Actual regularity makes the tangent-normal frame nonsingular; it is not
an independent matrix assumption. The frame need not be unit speed. -/
theorem relativeSaddleSeam_frame_det (z : ℂ) :
    (seamFrame (seamComplexCoord z) (seamComplexCoord (Complex.I * z))).det = ‖z‖^2 := by
  rw [Matrix.det_fin_two, Complex.sq_norm, Complex.normSq_apply]
  simp [seamFrame, seamComplexCoord_apply, Complex.mul_re, Complex.mul_im]

/-- A pair of actual matching first jets supplies the displayed common second
jet in ver500, with no assumed mixed- or tangential-entry agreement. -/
theorem relativeSaddleSeam_common_second_jets {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ ∞ γ) {f g : Coord → ℝ} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) (hU : IsOpen U)
    (hSeam : ∀ s, seamComplexCoord (γ s) ∈ U)
    (hGradient : ∀ s, planarGradient f (seamComplexCoord (γ s)) =
      planarGradient g (seamComplexCoord (γ s))) (s : ℝ) :
    let p := seamComplexCoord (γ s)
    let u := seamComplexCoord (deriv γ s)
    let v := seamComplexCoord (Complex.I * deriv γ s)
    seamFramedHessian f p u v = seamSecondJet
      (seamFramedHessian f p u v 0 0) (seamFramedHessian f p u v 1 0)
      (seamFramedHessian f p u v 1 1) ∧
    seamFramedHessian g p u v = seamSecondJet
      (seamFramedHessian f p u v 0 0) (seamFramedHessian f p u v 1 0)
      (seamFramedHessian g p u v 1 1) := by
  dsimp only
  refine ⟨seamFramedHessian_eq_secondJet hf hU (hSeam s) _ _, ?_⟩
  have he := seamFramedHessian_eq_secondJet hg hU (hSeam s)
    (seamComplexCoord (deriv γ s)) (seamComplexCoord (Complex.I * deriv γ s))
  rw [← relativeSaddleSeam_shared_entries hγ hf hg hU hSeam hGradient s 0,
    ← relativeSaddleSeam_shared_entries hγ hf hg hU hSeam hGradient s 1] at he
  exact he

end
end TightVer401
