import TightVer401.FermiGraphSmoothConvergence
import TightVer401.FermiSupportPerturbedMean

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Matrix
set_option backward.isDefEq.respectTransparency false

theorem fermiPerturbedSupport_profile_contDiff {κ χ : ℝ → ℝ}
    {H : Coord → ℝ} {U : Set Coord}
    (hκ : ContDiff ℝ ∞ κ) (hχ : ContDiff ℝ ∞ χ) (hχ0 : χ 0 = 1)
    (hU : IsOpen U) (hH : ContDiffOn ℝ ∞ H U)
    (hscale : ∀ p ∈ U, fermiNormalScale κ p ≠ 0)
    (hseam : ∀ r, (![r,0] : Coord) ∈ U)
    (hpos : ∀ r, 0 < fermiSeamMixed κ H r) (ε P : ℝ) :
    ContDiff ℝ ∞ (exitPositiveGraphProfile P
      (fermiSupportSeamSlope κ (fermiPerturbedSupport ε κ H χ))) := by
  have hac := fermiSeam_coefficients_smooth hκ hU hH hscale hseam
  have he := (fermiPerturbedSupport_seam_coefficients hκ hχ hχ0 hU hH hscale hseam hpos ε).2.2
  apply exitPositiveGraphProfile_contDiff
  rw [he]
  exact (fermiSeamSlopeCoefficient_contDiff hac.1 hκ hac.2 hpos).sub
    (contDiff_const.mul (hκ.pow 2))

/-- Every finite-order actual derivative of the exit graph tends uniformly to the
corresponding seam derivative on a full period. -/
theorem fermiExit_graph_uniform_smooth_convergence {ζ : ℝ → Ambient} {χ : ℝ → ℝ}
    {H : Coord → ℝ} {U : Set Coord}
    (hζ : ContDiff ℝ ∞ ζ) (hχ : ContDiff ℝ ∞ χ) (hχ0 : χ 0 = 1)
    (hU : IsOpen U) (hH : ContDiffOn ℝ ∞ H U)
    (hscale : ∀ p ∈ U, fermiNormalScale (normalLoopCurvature ζ) p ≠ 0)
    (hseam : ∀ r, (![r,0] : Coord) ∈ U)
    (hpos : ∀ r, 0 < fermiSeamMixed (normalLoopCurvature ζ) H r)
    (ε P : ℝ) (n : ℕ) {η : ℝ} (hη : 0 < η) :
    let v := exitPositiveGraphProfile P (fermiSupportSeamSlope (normalLoopCurvature ζ)
      (fermiPerturbedSupport ε (normalLoopCurvature ζ) H χ))
    ∃ e > 0, ∀ δ : ℝ, |δ| < e → ∀ r ∈ Icc (0 : ℝ) P,
      ‖iteratedFDeriv ℝ n (fun s : ℝ => fermiNormalMap ζ (exitGraphCurve v δ s)) r -
        iteratedFDeriv ℝ n ζ r‖ < η := by
  exact fermiGraph_uniform_smooth_convergence hζ
    (fermiPerturbedSupport_profile_contDiff (normalLoop_actual_smooth hζ).2
      hχ hχ0 hU hH hscale hseam hpos ε P) n hη

end
end TightVer401
