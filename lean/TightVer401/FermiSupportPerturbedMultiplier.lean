import TightVer401.FermiSupportPerturbedMean

namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.SmoothLocal.Geometry
open scoped ContDiff Matrix
set_option backward.isDefEq.respectTransparency false

theorem fermiPerturbedSupport_linearMultiplier {κ χ : ℝ → ℝ}
    {H : Coord → ℝ} {U : Set Coord} {P : ℝ}
    (hP : 0 < P) (hκ : ContDiff ℝ ∞ κ) (hχ : ContDiff ℝ ∞ χ) (hχ0 : χ 0 = 1)
    (hU : IsOpen U) (hH : ContDiffOn ℝ ∞ H U)
    (hscale : ∀ p ∈ U, fermiNormalScale κ p ≠ 0)
    (hseam : ∀ r, (![r,0] : Coord) ∈ U)
    (hpos : ∀ r, 0 < fermiSeamMixed κ H r)
    (hm : exitGraphMean P (fermiSupportSeamSlope κ H) = 0) (ε : ℝ) :
    fermiSeamLinearMultiplier P (fermiSeamMixed κ (fermiPerturbedSupport ε κ H χ))
      κ (fermiSeamNormal (fermiPerturbedSupport ε κ H χ)) =
      Real.exp (-(ε / 2 * ∫ r in 0..P, (κ r)^2)) := by
  have hac := fermiSeam_coefficients_smooth hκ hU hH hscale hseam
  have hc := fermiPerturbedSupport_seam_coefficients hκ hχ hχ0 hU hH hscale hseam hpos ε
  have hb : (∫ r in 0..P, fermiSupportSeamSlope κ H r) = 0 :=
    (div_eq_zero_iff.mp hm).resolve_right hP.ne'
  rw [hc.1,hc.2.1,fermiSeamLinearMultiplier_perturbation hac.1 hκ hac.2 hpos P ε]
  change Real.exp (∫ r in 0..P, fermiSupportSeamSlope κ H r) * _ = _
  rw [hb,Real.exp_zero,one_mul]

theorem fermiPerturbed_multiplier_attracting_iff {κ : ℝ → ℝ} {P ε : ℝ}
    (hmass : 0 < ∫ r in 0..P, (κ r)^2) :
    Real.exp (-(ε / 2 * ∫ r in 0..P, (κ r)^2)) < 1 ↔ 0 < ε := by
  rw [Real.exp_lt_one_iff,neg_lt_zero]
  constructor
  · intro h
    nlinarith
  · intro h
    exact mul_pos (div_pos h (by norm_num)) hmass

theorem fermiPerturbed_multiplier_repelling_iff {κ : ℝ → ℝ} {P ε : ℝ}
    (hmass : 0 < ∫ r in 0..P, (κ r)^2) :
    1 < Real.exp (-(ε / 2 * ∫ r in 0..P, (κ r)^2)) ↔ ε < 0 := by
  rw [Real.one_lt_exp_iff,neg_pos]
  constructor
  · intro h
    nlinarith
  · intro h
    exact mul_neg_of_neg_of_pos (div_neg_of_neg_of_pos h (by norm_num)) hmass

end
end TightVer401
