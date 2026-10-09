import TightVer401.FermiSupportReturnVariation
import TightVer401.ScalarFlowPeriodReturn

namespace TightVer401
noncomputable section
open Set Filter MeasureTheory OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

theorem exists_fermiSupport_full_period_flow {κ : ℝ → ℝ} {H : Coord → ℝ}
    {U : Set Coord} {P : ℝ}
    (hP : 0 < P) (hκ : ContDiff ℝ ∞ κ)
    (hU : IsOpen U) (hH : ContDiffOn ℝ ∞ H U)
    (hscale : ∀ p ∈ U, fermiNormalScale κ p ≠ 0)
    (hseam : ∀ r, (![r,0] : Coord) ∈ U)
    (hzero : ∀ r, fermiSupportL κ H ![r,0] = 0)
    (hpos : ∀ r, 0 < fermiSeamMixed κ H r) :
    ∃ (V : Set Coord) (u : Coord → ℝ), IsOpen V ∧ ContDiffOn ℝ ∞ u V ∧
      (∀ q ∈ V, (![q 0,u q] : Coord) ∈ U) ∧
      (∀ q ∈ V, coordPartial 0 u q = fermiSupportAsymptoticSlope κ H ![q 0,u q]) ∧
      (∀ r ∈ Icc (0 : ℝ) P, (![r,0] : Coord) ∈ V) ∧
      (∀ r ∈ Icc (0 : ℝ) P, u ![r,0] = 0) ∧
      ((fun x : ℝ => u ![0,x]) =ᶠ[𝓝 (0 : ℝ)] id) ∧
      HasDerivAt (fun x : ℝ => u ![P,x])
        (fermiSeamLinearMultiplier P (fermiSeamMixed κ H) κ (fermiSeamNormal H)) 0 ∧
      (∀ q ∈ V, (sphereSupportTensor (fermiMetric (fermiNormalScale κ)) H ![q 0,u q]).det < 0) := by
  obtain ⟨W,hW,hWU,hWs,hf,hdet,hquad⟩ :=
    exists_fermiSupport_asymptotic_domain hκ hU hH hscale hseam hzero hpos
  have hfzero (r : ℝ) : fermiSupportAsymptoticSlope κ H ![r,0] = 0 := by
    simp only [fermiSupportAsymptoticSlope,fermiAsymptoticSlope,hzero r,neg_zero,zero_div]
  obtain ⟨V,u,hV,hu,himage,hode,hvs,huzero,hi,hd⟩ :=
    exists_scalarFlowPeriod_return_family hP hW hf hWs hfzero
  have hc : scalarFlowLinearCoefficient (fermiSupportAsymptoticSlope κ H) =
      fermiSupportSeamSlope κ H := by
    funext r
    exact (fermiSupport_local_seam_slope_coefficient hκ hU hH hscale
      (hseam r) (hzero r) (hpos r)).2
  change HasDerivAt (fun x : ℝ => u ![P,x])
    (Real.exp (∫ r in 0..P, scalarFlowLinearCoefficient (fermiSupportAsymptoticSlope κ H) r)) 0 at hd
  rw [hc] at hd
  exact ⟨V,u,hV,hu,fun q hq => hWU (himage q hq),hode,hvs,huzero,hi,hd,
    fun q hq => hdet _ (himage q hq)⟩

end
end TightVer401
