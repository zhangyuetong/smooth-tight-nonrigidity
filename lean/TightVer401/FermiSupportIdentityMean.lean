import TightVer401.FermiSupportReturnVariation

namespace TightVer401
noncomputable section
open Set Filter MeasureTheory OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

theorem fermiSupport_actual_identity_return_mean_zero {κ : ℝ → ℝ} {H u : Coord → ℝ}
    {U V : Set Coord} {P : ℝ}
    (hP : 0 ≤ P) (hκ : ContDiff ℝ ∞ κ)
    (hU : IsOpen U) (hH : ContDiffOn ℝ ∞ H U)
    (hscale : ∀ p ∈ U, fermiNormalScale κ p ≠ 0)
    (hseam : ∀ r, (![r,0] : Coord) ∈ U)
    (hzero : ∀ r, fermiSupportL κ H ![r,0] = 0)
    (hpos : ∀ r, 0 < fermiSeamMixed κ H r)
    (hV : IsOpen V) (hu : ContDiffOn ℝ ∞ u V)
    (hode : ∀ q ∈ V, coordPartial 0 u q = fermiSupportAsymptoticSlope κ H ![q 0,u q])
    (hvs : ∀ r ∈ Icc (0 : ℝ) P, (![r,0] : Coord) ∈ V)
    (huzero : ∀ r ∈ Icc (0 : ℝ) P, u ![r,0] = 0)
    (hinitial : (fun x : ℝ => u ![0,x]) =ᶠ[𝓝 (0 : ℝ)] id)
    (hreturn : (fun x : ℝ => u ![P,x]) =ᶠ[𝓝 (0 : ℝ)] id) :
    exitGraphMean P (fermiSupportSeamSlope κ H) = 0 := by
  obtain ⟨W,hW,hWU,hWs,hf,hdet,hquad⟩ :=
    exists_fermiSupport_asymptotic_domain hκ hU hH hscale hseam hzero hpos
  let F : Coord → Coord := fun q => ![q 0,u q]
  have hF : ContDiffOn ℝ ∞ F V := by
    apply contDiffOn_pi.mpr
    intro i
    fin_cases i
    · exact (contDiff_apply ℝ ℝ 0).contDiffOn
    · exact hu
  let D := V ∩ F ⁻¹' W
  have hD : IsOpen D := hF.continuousOn.isOpen_inter_preimage hV hW
  have hDs (r : ℝ) (hr : r ∈ Icc (0 : ℝ) P) : (![r,0] : Coord) ∈ D := by
    refine ⟨hvs r hr,?_⟩
    change (![r,u ![r,0]] : Coord) ∈ W
    rw [huzero r hr]
    exact hWs r
  have hi := scalarFlow_return_identity_integral_zero hP hD hW (hu.mono inter_subset_left)
    hf (fun q hq => hq.2) (fun q hq => hode q hq.1) hDs huzero hinitial hreturn
  have hc : scalarFlowLinearCoefficient (fermiAsymptoticSlope (fermiSupportL κ H)
      (fermiSupportM κ H) (fermiSupportN H)) = fermiSupportSeamSlope κ H := by
    funext r
    exact (fermiSupport_local_seam_slope_coefficient hκ hU hH hscale
      (hseam r) (hzero r) (hpos r)).2
  rw [hc] at hi
  exact div_eq_zero_iff.mpr (Or.inl hi)

end
end TightVer401
