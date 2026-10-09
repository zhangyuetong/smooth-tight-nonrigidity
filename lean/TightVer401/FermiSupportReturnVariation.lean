import TightVer401.FermiSupportAsymptoticDomain
import TightVer401.FermiSupportPerturbedMean
import TightVer401.ScalarFlowVariationMultiplier

namespace TightVer401
noncomputable section
open Set Filter MeasureTheory OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

def fermiSupportAsymptoticSlope (κ : ℝ → ℝ) (H : Coord → ℝ) : Coord → ℝ :=
  fermiAsymptoticSlope (fermiSupportL κ H) (fermiSupportM κ H) (fermiSupportN H)

theorem fermiSupport_flow_return_hasDerivAt {κ : ℝ → ℝ} {H u : Coord → ℝ}
    {U V W : Set Coord} {P : ℝ}
    (hP : 0 ≤ P) (hκ : ContDiff ℝ ∞ κ)
    (hU : IsOpen U) (hH : ContDiffOn ℝ ∞ H U)
    (hscale : ∀ p ∈ U, fermiNormalScale κ p ≠ 0)
    (hHseam : ∀ r, (![r,0] : Coord) ∈ U)
    (hLzero : ∀ r, fermiSupportL κ H ![r,0] = 0)
    (hMpos : ∀ r, 0 < fermiSeamMixed κ H r)
    (hV : IsOpen V) (hW : IsOpen W) (hWU : W ⊆ U)
    (hu : ContDiffOn ℝ ∞ u V)
    (hdisc : ∀ p ∈ W, 0 < (fermiSupportM κ H p)^2 - fermiSupportL κ H p * fermiSupportN H p)
    (hmixed : ∀ p ∈ W, 0 < fermiSupportM κ H p)
    (himage : ∀ q ∈ V, (![q 0,u q] : Coord) ∈ W)
    (hode : ∀ q ∈ V, coordPartial 0 u q = fermiSupportAsymptoticSlope κ H ![q 0,u q])
    (huseam : ∀ r ∈ Icc (0 : ℝ) P, (![r,0] : Coord) ∈ V)
    (huzero : ∀ r ∈ Icc (0 : ℝ) P, u ![r,0] = 0)
    (hinitial : (fun x : ℝ => u ![0,x]) =ᶠ[𝓝 (0 : ℝ)] id) :
    HasDerivAt (fun x : ℝ => u ![P,x])
      (fermiSeamLinearMultiplier P (fermiSeamMixed κ H) κ (fermiSeamNormal H)) 0 := by
  have hc := fermiSupport_contDiffOn hκ hU hH hscale
  have hf : ContDiffOn ℝ ∞ (fermiSupportAsymptoticSlope κ H) W :=
    fermiAsymptoticSlope_contDiffOn (hc.1.mono hWU) (hc.2.1.mono hWU)
      (hc.2.2.mono hWU) hdisc hmixed
  have he : scalarFlowLinearCoefficient (fermiSupportAsymptoticSlope κ H) =
      fermiSupportSeamSlope κ H := by
    funext r
    exact (fermiSupport_local_seam_slope_coefficient hκ hU hH hscale
      (hHseam r) (hLzero r) (hMpos r)).2
  have hd := scalarFlow_return_hasDerivAt hP hV hW hu hf himage hode huseam huzero hinitial
  rw [he] at hd
  exact hd

theorem fermiSupport_identity_return_mean_zero {κ : ℝ → ℝ} {H u : Coord → ℝ}
    {U V W : Set Coord} {P : ℝ}
    (hP : 0 ≤ P) (hκ : ContDiff ℝ ∞ κ)
    (hU : IsOpen U) (hH : ContDiffOn ℝ ∞ H U)
    (hscale : ∀ p ∈ U, fermiNormalScale κ p ≠ 0)
    (hHseam : ∀ r, (![r,0] : Coord) ∈ U)
    (hLzero : ∀ r, fermiSupportL κ H ![r,0] = 0)
    (hMpos : ∀ r, 0 < fermiSeamMixed κ H r)
    (hV : IsOpen V) (hW : IsOpen W) (hWU : W ⊆ U)
    (hu : ContDiffOn ℝ ∞ u V)
    (hdisc : ∀ p ∈ W, 0 < (fermiSupportM κ H p)^2 - fermiSupportL κ H p * fermiSupportN H p)
    (hmixed : ∀ p ∈ W, 0 < fermiSupportM κ H p)
    (himage : ∀ q ∈ V, (![q 0,u q] : Coord) ∈ W)
    (hode : ∀ q ∈ V, coordPartial 0 u q = fermiSupportAsymptoticSlope κ H ![q 0,u q])
    (huseam : ∀ r ∈ Icc (0 : ℝ) P, (![r,0] : Coord) ∈ V)
    (huzero : ∀ r ∈ Icc (0 : ℝ) P, u ![r,0] = 0)
    (hinitial : (fun x : ℝ => u ![0,x]) =ᶠ[𝓝 (0 : ℝ)] id)
    (hreturn : (fun x : ℝ => u ![P,x]) =ᶠ[𝓝 (0 : ℝ)] id) :
    exitGraphMean P (fermiSupportSeamSlope κ H) = 0 := by
  have hd := fermiSupport_flow_return_hasDerivAt hP hκ hU hH hscale
    hHseam hLzero hMpos hV hW hWU hu hdisc hmixed himage hode huseam huzero hinitial
  have he := hd.unique ((hasDerivAt_id (0 : ℝ)).congr_of_eventuallyEq hreturn)
  have hl := congrArg Real.log he
  simp only [fermiSeamLinearMultiplier, Real.log_exp, Real.log_one] at hl
  exact div_eq_zero_iff.mpr (Or.inl hl)

end
end TightVer401
