import TightVer401.ExitPositiveGraphQuadratic
import Mathlib.Algebra.Order.ToIntervalMod

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

theorem exitGraphQuadratic_uniform_sign {ℓ M N : Coord → ℝ} {v a b : ℝ → ℝ}
    {U : Set Coord} {P m : ℝ} (hU : IsOpen U)
    (hℓ : ContDiffOn ℝ ∞ ℓ U) (hM : ContDiffOn ℝ ∞ M U) (hN : ContDiffOn ℝ ∞ N U)
    (hv : ContDiff ℝ ∞ v) (hvpos : ∀ r, 0 < v r) (hm : m ≠ 0)
    (hseam : ∀ r ∈ Icc (0 : ℝ) P, (![r, 0] : Coord) ∈ U)
    (hzero : ∀ r ∈ Icc (0 : ℝ) P, ℓ ![r, 0] = 0)
    (hMr : ∀ r ∈ Icc (0 : ℝ) P, M ![r, 0] = a r)
    (ha : ∀ r ∈ Icc (0 : ℝ) P, 0 < a r)
    (hℓt : ∀ r ∈ Icc (0 : ℝ) P, coordPartial 1 ℓ ![r, 0] = -2 * a r * b r)
    (hode : ∀ r ∈ Icc (0 : ℝ) P, deriv v r = (b r - m) * v r) :
    ∃ ε > 0, ∀ r ∈ Icc (0 : ℝ) P, ∀ δ, |δ| < ε → δ * m < 0 →
      0 < exitGraphQuadratic ℓ M N v ![r, δ] := by
  let V := (exitGraphPoint v) ⁻¹' U
  have hV : IsOpen V := hU.preimage (exitGraphPoint_contDiff hv).continuous
  have hF := exitGraphQuadratic_contDiffOn hℓ hM hN hv
  have hseam' : ∀ r ∈ Icc (0 : ℝ) P, (![r, 0] : Coord) ∈ V := by
    intro r hr
    simpa [V, exitGraphPoint] using hseam r hr
  have hzero' : ∀ r ∈ Icc (0 : ℝ) P, exitGraphQuadratic ℓ M N v ![r, 0] = 0 :=
    fun r hr => exitGraphQuadratic_seam (hzero r hr)
  have hderiv : ∀ r ∈ Icc (0 : ℝ) P,
      coordPartial 1 (exitGraphQuadratic ℓ M N v) ![r, 0] = -2 * a r * m * v r :=
    fun r hr => exitGraphQuadratic_transverse_seam hU hℓ hM hN hv
      (hseam r hr) (hMr r hr) (hℓt r hr) (hode r hr)
  rcases lt_or_gt_of_ne hm with hmneg | hmpos
  · have hpos : ∀ r ∈ Icc (0 : ℝ) P,
        0 < coordPartial 1 (exitGraphQuadratic ℓ M N v) ![r, 0] := by
      intro r hr
      rw [hderiv r hr]
      have h := mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2)
        (ha r hr)) (neg_pos.mpr hmneg)) (hvpos r)
      have he : -2 * a r * m * v r = 2 * a r * (-m) * v r := by ring
      rw [he]
      exact h
    obtain ⟨ε, hε, he⟩ := exitGraph_uniform_positive_side hV hF hseam' hzero' hpos
    refine ⟨ε, hε, ?_⟩
    intro r hr δ hδ hsign
    have hδpos : 0 < δ := by
      rcases mul_neg_iff.mp hsign with h | h
      · exact h.1
      · exact False.elim (hmneg.not_gt h.2)
    exact he r hr δ hδpos (lt_of_le_of_lt (le_abs_self δ) hδ)
  · have hneg : ∀ r ∈ Icc (0 : ℝ) P,
        coordPartial 1 (exitGraphQuadratic ℓ M N v) ![r, 0] < 0 := by
      intro r hr
      rw [hderiv r hr]
      have h := mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2)
        (ha r hr)) hmpos) (hvpos r)
      nlinarith
    obtain ⟨ε, hε, he⟩ := exitGraph_uniform_negative_side hV hF hseam' hzero' hneg
    refine ⟨ε, hε, ?_⟩
    intro r hr δ hδ hsign
    have hδneg : δ < 0 := by
      rcases mul_neg_iff.mp hsign with h | h
      · exact False.elim (hmpos.not_gt h.2)
      · exact h.1
    exact he r hr δ (abs_lt.mp hδ).1 hδneg

theorem exitGraphQuadratic_periodic {ℓ M N : Coord → ℝ} {v : ℝ → ℝ} {P : ℝ}
    (hℓ : ∀ t, Function.Periodic (fun r => ℓ ![r, t]) P)
    (hM : ∀ t, Function.Periodic (fun r => M ![r, t]) P)
    (hN : ∀ t, Function.Periodic (fun r => N ![r, t]) P)
    (hv : Function.Periodic v P) (δ : ℝ) :
    Function.Periodic (fun r => exitGraphQuadratic ℓ M N v ![r, δ]) P := by
  intro r
  simp only [exitGraphQuadratic, exitGraphPoint, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, hv r, deriv_periodic hv r]
  simp only [hℓ (δ * v r) r, hM (δ * v r) r, hN (δ * v r) r]

theorem exitGraph_periodic_positive_of_period {F : ℝ → ℝ} {P : ℝ}
    (hP : 0 < P) (hp : Function.Periodic F P) (hF : ∀ r ∈ Icc (0 : ℝ) P, 0 < F r) :
    ∀ r, 0 < F r := by
  intro r
  let s := toIcoMod hP 0 r
  have hs : s ∈ Icc (0 : ℝ) P := Ico_subset_Icc_self (toIcoMod_mem_Ico' hP r)
  have he : F r = F s := by
    conv_lhs => rw [← toIcoMod_add_toIcoDiv_zsmul hP 0 r]
    exact hp.zsmul (toIcoDiv hP 0 r) s
  rw [he]
  exact hF s hs

theorem exitPositiveGraph_uniform_sign {ℓ M N : Coord → ℝ} {a b : ℝ → ℝ}
    {U : Set Coord} {P : ℝ} (hP : 0 < P)
    (hb : ContDiff ℝ ∞ b) (hbp : Function.Periodic b P)
    (hU : IsOpen U) (hℓ : ContDiffOn ℝ ∞ ℓ U)
    (hM : ContDiffOn ℝ ∞ M U) (hN : ContDiffOn ℝ ∞ N U)
    (hℓp : ∀ t, Function.Periodic (fun r => ℓ ![r, t]) P)
    (hMp : ∀ t, Function.Periodic (fun r => M ![r, t]) P)
    (hNp : ∀ t, Function.Periodic (fun r => N ![r, t]) P)
    (hm : exitGraphMean P b ≠ 0)
    (hseam : ∀ r ∈ Icc (0 : ℝ) P, (![r, 0] : Coord) ∈ U)
    (hzero : ∀ r ∈ Icc (0 : ℝ) P, ℓ ![r, 0] = 0)
    (hMr : ∀ r ∈ Icc (0 : ℝ) P, M ![r, 0] = a r)
    (ha : ∀ r ∈ Icc (0 : ℝ) P, 0 < a r)
    (hℓt : ∀ r ∈ Icc (0 : ℝ) P, coordPartial 1 ℓ ![r, 0] = -2 * a r * b r) :
    ∃ ε > 0, ∀ δ, |δ| < ε → δ * exitGraphMean P b < 0 →
      ∀ r, 0 < exitGraphQuadratic ℓ M N (exitPositiveGraphProfile P b) ![r, δ] := by
  obtain ⟨ε, hε, he⟩ := exitGraphQuadratic_uniform_sign hU hℓ hM hN
    (exitPositiveGraphProfile_contDiff hb) (exitPositiveGraphProfile_pos P b)
    hm hseam hzero hMr ha hℓt (fun r _ => exitPositiveGraphProfile_deriv hb r)
  refine ⟨ε, hε, ?_⟩
  intro δ hδ hsign
  apply exitGraph_periodic_positive_of_period hP
    (exitGraphQuadratic_periodic hℓp hMp hNp (exitPositiveGraphProfile_periodic hP hb hbp) δ)
  exact fun r hr => he r hr δ hδ hsign

end
end TightVer401
