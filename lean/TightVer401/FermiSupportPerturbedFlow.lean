import TightVer401.FermiSupportFlowExistence
import TightVer401.FermiSupportPerturbedMultiplier
import TightVer401.ScalarReturnRepulsion

namespace TightVer401
noncomputable section
open Set Filter MeasureTheory OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

theorem exists_fermiPerturbedSupport_hyperbolic_flow {κ χ : ℝ → ℝ}
    {H : Coord → ℝ} {U : Set Coord} {P : ℝ}
    (hP : 0 < P) (hκ : ContDiff ℝ ∞ κ) (hχ : ContDiff ℝ ∞ χ) (hχ0 : χ 0 = 1)
    (hU : IsOpen U) (hH : ContDiffOn ℝ ∞ H U)
    (hscale : ∀ p ∈ U, fermiNormalScale κ p ≠ 0)
    (hseam : ∀ r, (![r,0] : Coord) ∈ U)
    (hzero : ∀ r, fermiSupportL κ H ![r,0] = 0)
    (hpos : ∀ r, 0 < fermiSeamMixed κ H r)
    (hm : exitGraphMean P (fermiSupportSeamSlope κ H) = 0)
    (hmass : 0 < ∫ r in 0..P, (κ r)^2) (ε : ℝ) :
    let Hε := fermiPerturbedSupport ε κ H χ
    ∃ (V : Set Coord) (u : Coord → ℝ), IsOpen V ∧ ContDiffOn ℝ ∞ u V ∧
      (∀ q ∈ V, (![q 0,u q] : Coord) ∈ U) ∧
      (∀ q ∈ V, coordPartial 0 u q = fermiSupportAsymptoticSlope κ Hε ![q 0,u q]) ∧
      (∀ r ∈ Icc (0 : ℝ) P, (![r,0] : Coord) ∈ V ∧ u ![r,0] = 0) ∧
      ((fun x : ℝ => u ![0,x]) =ᶠ[𝓝 (0 : ℝ)] id) ∧
      HasDerivAt (fun x : ℝ => u ![P,x])
        (Real.exp (-(ε / 2 * ∫ r in 0..P, (κ r)^2))) 0 ∧
      (0 < ε → ∃ e > 0, ∀ x : ℝ, |x| < e →
        (∀ n : ℕ, |((fun y : ℝ => u ![P,y])^[n]) x| < e) ∧
        Tendsto (fun n : ℕ => ((fun y : ℝ => u ![P,y])^[n]) x) atTop (𝓝 0)) ∧
      (ε < 0 → ∃ e > 0, ∀ x : ℝ, x ≠ 0 → |x| < e →
        ∃ n : ℕ, e ≤ |((fun y : ℝ => u ![P,y])^[n]) x|) := by
  let Hε := fermiPerturbedSupport ε κ H χ
  have ha := (fermiSeam_coefficients_smooth hκ hU hH hscale hseam).1
  have hHε : ContDiffOn ℝ ∞ Hε U :=
    hH.add (fermiSeamPerturbation_contDiff ha hκ hχ ε).contDiffOn
  have hj (r) := fermiSeamPerturbation_preserves_support_seam ha hκ hχ hχ0 hU hH ε (hseam r)
  have hzeroε (r) : fermiSupportL κ Hε ![r,0] = 0 := (hj r).1.trans (hzero r)
  have hposε (r) : 0 < fermiSeamMixed κ Hε r := by
    have he : fermiSeamMixed κ Hε r = fermiSeamMixed κ H r := (hj r).2.1
    rw [he]
    exact hpos r
  obtain ⟨V,u,hV,hu,himage,hode,hvs,huzero,hi,hd,hdet⟩ :=
    exists_fermiSupport_full_period_flow hP hκ hU hHε hscale hseam hzeroε hposε
  rw [fermiPerturbedSupport_linearMultiplier hP hκ hχ hχ0 hU hH hscale hseam hpos hm ε] at hd
  have hRzero : u ![P,0] = 0 := huzero P ⟨hP.le,le_rfl⟩
  exact ⟨V,u,hV,hu,himage,hode,fun r hr => ⟨hvs r hr,huzero r hr⟩,hi,hd,
    fun hε => scalarReturn_attracts hd hRzero (Real.exp_pos _)
      ((fermiPerturbed_multiplier_attracting_iff hmass).mpr hε),
    fun hε => scalarReturn_repels hd hRzero
      ((fermiPerturbed_multiplier_repelling_iff hmass).mpr hε)⟩

end
end TightVer401
