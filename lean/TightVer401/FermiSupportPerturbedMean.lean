import TightVer401.FermiSeamCoefficient
import TightVer401.FermiPerturbationCollar
import TightVer401.ExitPositiveGraphProfile

namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.SmoothLocal.Geometry
open scoped ContDiff Matrix
set_option backward.isDefEq.respectTransparency false

def fermiSupportSeamSlope (κ : ℝ → ℝ) (H : Coord → ℝ) : ℝ → ℝ :=
  fermiSeamSlopeCoefficient (fermiSeamMixed κ H) κ (fermiSeamNormal H)

def fermiPerturbedSupport (ε : ℝ) (κ : ℝ → ℝ) (H : Coord → ℝ) (χ : ℝ → ℝ) : Coord → ℝ :=
  fun p => H p + fermiSeamPerturbation ε (fermiSeamMixed κ H) κ χ p

theorem fermiPerturbedSupport_seam_coefficients {κ χ : ℝ → ℝ}
    {H : Coord → ℝ} {U : Set Coord}
    (hκ : ContDiff ℝ ∞ κ) (hχ : ContDiff ℝ ∞ χ) (hχ0 : χ 0 = 1)
    (hU : IsOpen U) (hH : ContDiffOn ℝ ∞ H U)
    (hscale : ∀ p ∈ U, fermiNormalScale κ p ≠ 0)
    (hseam : ∀ r, (![r,0] : Coord) ∈ U)
    (hpos : ∀ r, 0 < fermiSeamMixed κ H r) (ε : ℝ) :
    fermiSeamMixed κ (fermiPerturbedSupport ε κ H χ) = fermiSeamMixed κ H ∧
    fermiSeamNormal (fermiPerturbedSupport ε κ H χ) =
      (fun r => fermiSeamNormal H r + ε * fermiSeamMixed κ H r * κ r) ∧
    fermiSupportSeamSlope κ (fermiPerturbedSupport ε κ H χ) =
      (fun r => fermiSupportSeamSlope κ H r - ε / 2 * (κ r)^2) := by
  have ha := (fermiSeam_coefficients_smooth hκ hU hH hscale hseam).1
  have hj (r) := fermiSeamPerturbation_preserves_support_seam ha hκ hχ hχ0 hU hH ε (hseam r)
  have heA : fermiSeamMixed κ (fermiPerturbedSupport ε κ H χ) = fermiSeamMixed κ H :=
    funext fun r => (hj r).2.1
  have heC : fermiSeamNormal (fermiPerturbedSupport ε κ H χ) =
      (fun r => fermiSeamNormal H r + ε * fermiSeamMixed κ H r * κ r) :=
    funext fun r => (hj r).2.2
  refine ⟨heA, heC, ?_⟩
  unfold fermiSupportSeamSlope
  rw [heA, heC]
  exact funext (fermiSeamSlopeCoefficient_perturbation hpos ε)

theorem fermiPerturbedSupport_mean {κ χ : ℝ → ℝ} {H : Coord → ℝ} {U : Set Coord}
    (hκ : ContDiff ℝ ∞ κ) (hχ : ContDiff ℝ ∞ χ) (hχ0 : χ 0 = 1)
    (hU : IsOpen U) (hH : ContDiffOn ℝ ∞ H U)
    (hscale : ∀ p ∈ U, fermiNormalScale κ p ≠ 0)
    (hseam : ∀ r, (![r,0] : Coord) ∈ U)
    (hpos : ∀ r, 0 < fermiSeamMixed κ H r) (P ε : ℝ) :
    exitGraphMean P (fermiSupportSeamSlope κ (fermiPerturbedSupport ε κ H χ)) =
      exitGraphMean P (fermiSupportSeamSlope κ H) -
        (ε / 2 * ∫ r in 0..P, (κ r)^2) / P := by
  have hac := fermiSeam_coefficients_smooth hκ hU hH hscale hseam
  have he := (fermiPerturbedSupport_seam_coefficients hκ hχ hχ0 hU hH hscale hseam hpos ε).2.2
  unfold exitGraphMean
  rw [he]
  unfold fermiSupportSeamSlope
  rw [intervalIntegral.integral_sub
    ((fermiSeamSlopeCoefficient_contDiff hac.1 hκ hac.2 hpos).continuous.intervalIntegrable 0 P)
    (((hκ.pow 2).continuous.const_mul (ε / 2)).intervalIntegrable 0 P),
    intervalIntegral.integral_const_mul, sub_div]

theorem fermiSupportSeamSlope_mean_zero {κ : ℝ → ℝ} {H : Coord → ℝ} {U : Set Coord} {P : ℝ}
    (hκ : ContDiff ℝ ∞ κ) (hU : IsOpen U) (hH : ContDiffOn ℝ ∞ H U)
    (hscale : ∀ p ∈ U, fermiNormalScale κ p ≠ 0)
    (hseam : ∀ r, (![r,0] : Coord) ∈ U)
    (hpos : ∀ r, 0 < fermiSeamMixed κ H r)
    (hκP : Function.Periodic κ P) (hHP : FermiPeriodic P H)
    (hperiod : (∫ r in 0..P, κ r * fermiSeamNormal H r / fermiSeamMixed κ H r) = 0) :
    exitGraphMean P (fermiSupportSeamSlope κ H) = 0 := by
  have hac := fermiSeam_coefficients_smooth hκ hU hH hscale hseam
  have hacP := fermiSeam_coefficients_periodic hκP hHP
  have he := fermiSeamSlopeCoefficient_period hac.1 hacP.1 hκ.continuous hac.2.continuous hpos
  rw [hperiod, mul_zero] at he
  exact div_eq_zero_iff.mpr (Or.inl he)

theorem fermiPerturbedSupport_mean_ne_zero {ζ : ℝ → Ambient} {χ : ℝ → ℝ}
    {H : Coord → ℝ} {U : Set Coord} {P ε : ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (hP : 0 < P) (hζP : Function.Periodic ζ P)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1)
    {e : Ambient} (hhemisphere : ∀ r, 0 < inner ℝ (ζ r) e)
    (hχ : ContDiff ℝ ∞ χ) (hχ0 : χ 0 = 1)
    (hU : IsOpen U) (hH : ContDiffOn ℝ ∞ H U)
    (hscale : ∀ p ∈ U, fermiNormalScale (normalLoopCurvature ζ) p ≠ 0)
    (hseam : ∀ r, (![r,0] : Coord) ∈ U)
    (hpos : ∀ r, 0 < fermiSeamMixed (normalLoopCurvature ζ) H r)
    (hm : exitGraphMean P (fermiSupportSeamSlope (normalLoopCurvature ζ) H) = 0)
    (hε : ε ≠ 0) :
    exitGraphMean P (fermiSupportSeamSlope (normalLoopCurvature ζ)
      (fermiPerturbedSupport ε (normalLoopCurvature ζ) H χ)) ≠ 0 := by
  have hmass := normalLoop_hemisphere_curvature_sq_period_pos hζ hP hζP hunit hspeed hhemisphere
  rw [fermiPerturbedSupport_mean (normalLoop_actual_smooth hζ).2 hχ hχ0
    hU hH hscale hseam hpos, hm, zero_sub]
  exact neg_ne_zero.mpr (div_ne_zero
    (mul_ne_zero (div_ne_zero hε (by norm_num)) hmass.ne') hP.ne')

end
end TightVer401
