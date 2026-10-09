import TightVer401.ExitPositiveGraphSign
import TightVer401.ExitPositiveGraphDomain

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

theorem exitGraph_exists_signed_small_scalar {m ε η : ℝ}
    (hm : m ≠ 0) (hε : 0 < ε) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < |δ| ∧ |δ| < ε ∧ |δ| < η ∧ δ * m < 0 := by
  let d := min ε η / 2
  have hd : 0 < d := div_pos (lt_min hε hη) (by norm_num)
  have hdε : d < ε := lt_of_lt_of_le (by dsimp [d]; linarith [lt_min hε hη]) (min_le_left ε η)
  have hdη : d < η := lt_of_lt_of_le (by dsimp [d]; linarith [lt_min hε hη]) (min_le_right ε η)
  rcases lt_or_gt_of_ne hm with hmneg | hmpos
  · exact ⟨d, by simpa [abs_of_pos hd] using hd,
      by simpa [abs_of_pos hd] using hdε,
      by simpa [abs_of_pos hd] using hdη, mul_neg_of_pos_of_neg hd hmneg⟩
  · exact ⟨-d, by simpa [abs_neg, abs_of_pos hd] using hd,
      by simpa [abs_neg, abs_of_pos hd] using hdε,
      by simpa [abs_neg, abs_of_pos hd] using hdη, mul_neg_of_neg_of_pos (neg_neg_of_pos hd) hmpos⟩

theorem exists_exitPositiveGraph_arbitrarily_small {ℓ M N : Coord → ℝ} {a b : ℝ → ℝ}
    {U : Set Coord} {P η : ℝ} (hP : 0 < P) (hη : 0 < η)
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
    ∃ δ : ℝ, 0 < |δ| ∧ |δ| < η ∧ δ * exitGraphMean P b < 0 ∧
      (∀ r ∈ Icc (0 : ℝ) P, exitGraphCurve (exitPositiveGraphProfile P b) δ r ∈ U) ∧
      ∀ r, 0 < exitGraphQuadratic ℓ M N (exitPositiveGraphProfile P b) ![r, δ] := by
  obtain ⟨ε, hε, he⟩ := exitPositiveGraph_uniform_sign hP hb hbp hU hℓ hM hN
    hℓp hMp hNp hm hseam hzero hMr ha hℓt
  obtain ⟨ε₀, hε₀, hdom⟩ := exitGraphCurve_uniform_domain
    (exitPositiveGraphProfile_contDiff hb) hU hseam
  obtain ⟨δ, hd, hdε, hdη, hsign⟩ := exitGraph_exists_signed_small_scalar hm (lt_min hε hε₀) hη
  refine ⟨δ, hd, hdη, hsign, ?_, he δ (lt_of_lt_of_le hdε (min_le_left _ _)) hsign⟩
  exact fun r hr => hdom r hr δ (le_of_lt (lt_of_lt_of_le hdε (min_le_right _ _)))

end
end TightVer401
